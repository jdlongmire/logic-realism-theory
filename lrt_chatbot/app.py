"""LRT Chatbot - Gradio frontend with security hardening.

Usage:
    # First, build the index:
    python -m lrt_chatbot.indexer --force

    # Then run the app:
    python -m lrt_chatbot.app
"""

import hashlib
import logging
import os
import time

import gradio as gr
from google import genai
from google.genai import types
from google.genai.errors import ClientError, ServerError

from . import config
from .retriever import Retriever
from .prompts import build_prompt
from .security import (
    sanitize_input,
    detect_injection,
    filter_output,
    sanitize_error,
    rate_limiter,
    daily_quota,
    audit_log,
    MAX_QUERY_LENGTH,
)

logger = logging.getLogger(__name__)

# Configure logging for security events
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s %(levelname)s %(name)s: %(message)s',
)

# Lazy globals
_retriever: Retriever | None = None
_gemini: genai.Client | None = None

# Injection refusal message. Deliberately vague to avoid
# teaching attackers what was detected.
_INJECTION_REFUSAL = (
    "I can only answer questions about Logic Realism Theory. "
    "Could you rephrase your question about LRT's ontology, "
    "derivation chain, formalization, or cosmology?"
)


def _get_retriever() -> Retriever:
    global _retriever
    if _retriever is None:
        _retriever = Retriever()
    return _retriever


def _get_gemini() -> genai.Client:
    global _gemini
    if _gemini is None:
        _gemini = genai.Client(api_key=config.GEMINI_API_KEY)
    return _gemini


def _session_id(request: gr.Request | None) -> str:
    """Derive a session identifier for rate limiting."""
    if request and hasattr(request, 'client') and request.client:
        raw = f'{request.client.host}:{request.headers.get("user-agent", "")}'
    else:
        raw = 'default-session'
    return hashlib.sha256(raw.encode()).hexdigest()[:16]


def chat(message: str, history: list, mode: str,
         request: gr.Request = None) -> str:
    """Handle a chat message with full security pipeline."""
    if not message.strip():
        return ''

    # --- Rate limiting ---
    sid = _session_id(request)
    allowed, rate_msg = rate_limiter.check(sid)
    if not allowed:
        audit_log.log('rate_limited', sid)
        return rate_msg

    # --- Daily quota check ---
    allowed, quota_msg = daily_quota.check(sid)
    if not allowed:
        audit_log.log('quota_exceeded', sid, global_count=daily_quota.global_count)
        return quota_msg

    # --- Input sanitization ---
    message, warnings = sanitize_input(message)
    for w in warnings:
        logger.info('Input sanitization [%s]: %s', sid, w)
        audit_log.log('sanitization', sid, warning=w)

    # --- Prompt injection detection ---
    is_suspicious, pattern_type = detect_injection(message)
    if is_suspicious:
        logger.warning('Blocked suspicious query [%s]: type=%s, query=%s',
                       sid, pattern_type, message[:200])
        audit_log.log('injection_blocked', sid, pattern=pattern_type,
                      query_prefix=message[:200])
        return _INJECTION_REFUSAL

    try:
        retriever = _get_retriever()
        client = _get_gemini()

        # Retrieve relevant context
        retrieved = retriever.query(message)
        standing = retriever.get_standing_context()

        # Build prompt
        mode_key = 'advocacy' if mode == 'Advocacy' else 'exposition'
        system_prompt, user_message = build_prompt(
            message, retrieved, standing, mode=mode_key
        )

        # Gemini safety settings: block dangerous content categories
        safety_settings = [
            types.SafetySetting(
                category='HARM_CATEGORY_DANGEROUS_CONTENT',
                threshold='BLOCK_LOW_AND_ABOVE',
            ),
            types.SafetySetting(
                category='HARM_CATEGORY_HARASSMENT',
                threshold='BLOCK_MEDIUM_AND_ABOVE',
            ),
        ]

        # Call Gemini with exponential backoff + cascading fallback
        models_to_try = [
            config.LLM_MODEL,
            config.LLM_FALLBACK_MODEL,
            'gemini-1.5-flash',
        ]
        response = None
        last_error = None
        for model_name in models_to_try:
            backoff_delays = [2, 5, 10]
            for attempt, delay in enumerate(backoff_delays):
                try:
                    response = client.models.generate_content(
                        model=model_name,
                        contents=[types.Content(
                            role='user',
                            parts=[types.Part.from_text(text=user_message)],
                        )],
                        config=types.GenerateContentConfig(
                            system_instruction=system_prompt,
                            temperature=0.3,
                            safety_settings=safety_settings,
                        ),
                    )
                    break
                except (ServerError, ClientError) as e:
                    last_error = e
                    if getattr(e, 'code', 0) in (503, 429):
                        logger.warning('Gemini %s attempt %d returned %d, '
                                       'retrying in %ds',
                                       model_name, attempt + 1, e.code, delay)
                        time.sleep(delay)
                        continue
                    raise
            if response is not None:
                break
        if response is None:
            logger.error('All models exhausted after retries: %s', last_error)
            return ('The language model is temporarily unavailable due to high demand. '
                    'Please try again in about 30 seconds.')

        result = ''
        for part in response.candidates[0].content.parts:
            if part.text:
                result += part.text

        # --- Output filtering ---
        result = filter_output(result)

        # --- Record successful query ---
        daily_quota.record(sid)
        audit_log.log('query', sid, mode=mode,
                      query_len=len(message), response_len=len(result),
                      query_preview=message[:80])

        return result

    except Exception as e:
        audit_log.log('error', sid, error=str(e)[:200])
        return sanitize_error(e)


_COOLDOWN_JS = """
() => {
    const observer = new MutationObserver(() => {
        const msgs = document.querySelectorAll('.message.bot .md');
        if (!msgs.length) return;
        const last = msgs[msgs.length - 1].textContent || '';
        if (last.includes('temporarily unavailable') || last.includes('try again')) {
            const btn = document.querySelector('#component-0 button.primary');
            if (btn && !btn.disabled) {
                btn.disabled = true;
                btn.style.opacity = '0.5';
                setTimeout(() => { btn.disabled = false; btn.style.opacity = '1'; }, 10000);
            }
        }
    });
    observer.observe(document.body, {childList: true, subtree: true});
}
"""


def create_app() -> gr.Blocks:
    """Create the Gradio app."""
    with gr.Blocks(
        title='LRT Chatbot',
        theme=gr.themes.Soft(),
        js=_COOLDOWN_JS,
    ) as app:
        gr.Markdown(
            '# Logic Realism Theory Chatbot\n'
            'Ask questions about LRT: the ontological framework, '
            'derivation chain, Lean formalization, and cosmology extension.\n\n'
            '*Exposition mode* explains neutrally. '
            '*Advocacy mode* argues from within the framework.'
        )

        with gr.Row():
            mode = gr.Radio(
                choices=['Exposition', 'Advocacy'],
                value='Exposition',
                label='Mode',
                scale=3,
            )
            new_chat_btn = gr.Button('🗨 New Chat', scale=1, variant='secondary')

        chatbot = gr.Chatbot(
            latex_delimiters=[
                {"left": "$$", "right": "$$", "display": True},
                {"left": "$", "right": "$", "display": False},
                {"left": "\\(", "right": "\\)", "display": False},
                {"left": "\\[", "right": "\\]", "display": True},
            ],
        )

        chat_interface = gr.ChatInterface(
            fn=chat,
            chatbot=chatbot,
            additional_inputs=[mode],
            examples=[
                ['What is the bridge equation and what is its epistemic status?'],
                ['How does LRT derive the Born rule?'],
                ['What is the current Lean formalization status?'],
                ['How does LRT handle the black hole information paradox?'],
                ['What are the main open problems in LRT?'],
                ['How does LRT compare to Hardy\'s reconstruction?'],
            ],
        )

        new_chat_btn.click(
            fn=lambda: ([], None),
            outputs=[chat_interface.chatbot, chat_interface.textbox],
        )

    return app


def main():
    """Launch the app (public access, protected by rate limiting + injection detection)."""
    app = create_app()

    logger.info('Launching LRT Chatbot (public mode)')
    app.launch(
        server_name='127.0.0.1',
        server_port=7860,
        share=False,
        root_path='/lrtchat',
    )


if __name__ == '__main__':
    main()
