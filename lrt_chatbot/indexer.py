"""LRT corpus indexer.

Chunks LRT repo content by type and stores embeddings in ChromaDB
using Gemini text-embedding-004.
"""

import re
import hashlib
from pathlib import Path

import yaml
import chromadb
from google import genai

from . import config
from .claims import ClaimRegistry


# --- Chunking ---

def _heading_split(text: str, max_chars: int = 3200) -> list[dict]:
    """Split markdown by h2/h3 headings, with fallback size splitting."""
    sections = []
    current_heading = ''
    current_lines = []

    for line in text.split('\n'):
        if re.match(r'^#{2,3}\s', line):
            if current_lines:
                sections.append({
                    'heading': current_heading,
                    'text': '\n'.join(current_lines).strip(),
                })
            current_heading = line.strip('# ').strip()
            current_lines = [line]
        else:
            current_lines.append(line)

    if current_lines:
        sections.append({
            'heading': current_heading,
            'text': '\n'.join(current_lines).strip(),
        })

    # Split oversized sections
    result = []
    for sec in sections:
        if len(sec['text']) <= max_chars:
            result.append(sec)
        else:
            # Split on paragraphs
            paragraphs = sec['text'].split('\n\n')
            buf = ''
            part = 1
            for para in paragraphs:
                if len(buf) + len(para) > max_chars and buf:
                    result.append({
                        'heading': f"{sec['heading']} (part {part})",
                        'text': buf.strip(),
                    })
                    part += 1
                    buf = para
                else:
                    buf = buf + '\n\n' + para if buf else para
            if buf.strip():
                result.append({
                    'heading': f"{sec['heading']} (part {part})" if part > 1 else sec['heading'],
                    'text': buf.strip(),
                })
    return result


def _lean_split(text: str) -> list[dict]:
    """Split Lean file by theorem/def/lemma/axiom blocks."""
    blocks = []
    current_symbol = ''
    current_lines = []
    symbol_pattern = re.compile(r'^(theorem|def|lemma|axiom|instance|structure|class)\s+(\S+)')

    for line in text.split('\n'):
        m = symbol_pattern.match(line)
        if m:
            if current_lines:
                blocks.append({
                    'heading': current_symbol or 'preamble',
                    'text': '\n'.join(current_lines).strip(),
                })
            current_symbol = f'{m.group(1)} {m.group(2)}'
            current_lines = [line]
        else:
            current_lines.append(line)

    if current_lines:
        blocks.append({
            'heading': current_symbol or 'preamble',
            'text': '\n'.join(current_lines).strip(),
        })
    return blocks


def _chunk_claim(data: dict) -> list[dict]:
    """Turn a claim YAML into a single chunk with rich text."""
    parts = [
        f"Claim {data.get('id', '?')}: {data.get('name', '?')}",
        f"Statement: {data.get('statement', '').strip()}",
        f"Role: {data.get('role', '?')}",
        f"Proof status: {data.get('proof_status', '?')}",
        f"Epistemic status: {data.get('epistemic_status', '?')}",
    ]
    deps = data.get('depends_on', [])
    if deps:
        dep_ids = [d.get('claim_id', '?') for d in deps]
        parts.append(f"Depends on: {', '.join(dep_ids)}")
    risk = data.get('risk_if_false', '')
    if risk:
        parts.append(f"Risk if false: {risk.strip()}")
    notes = data.get('notes', '')
    if notes:
        parts.append(f"Notes: {notes.strip()}")
    return [{'heading': data.get('id', 'claim'), 'text': '\n'.join(parts)}]


def chunk_file(path: Path, content_type: str) -> list[dict]:
    """Chunk a single file. Returns list of {heading, text, metadata}."""
    try:
        raw = path.read_text(errors='replace')
    except Exception:
        return []

    if not raw.strip():
        return []

    if content_type == 'claim':
        data = yaml.safe_load(raw) or {}
        sections = _chunk_claim(data)
    elif content_type == 'lean':
        sections = _lean_split(raw)
    else:
        sections = _heading_split(raw)

    # Attach metadata and filter empties
    registry = ClaimRegistry()
    rel_path = str(path.relative_to(config.LRT_REPO_ROOT))
    chunks = []
    for sec in sections:
        text = sec['text']
        if len(text.strip()) < 20:
            continue
        claim_ids = registry.extract_claim_ids(text)
        chunks.append({
            'text': text,
            'metadata': {
                'source_file': rel_path,
                'section_heading': sec['heading'],
                'content_type': content_type,
                'referenced_claims': ','.join(claim_ids) if claim_ids else '',
            },
        })
    return chunks


def gather_all_chunks() -> list[dict]:
    """Gather chunks from all configured content sources."""
    all_chunks = []
    for name, pattern, content_type in config.CONTENT_SOURCES:
        paths = sorted(config.LRT_REPO_ROOT.glob(pattern))
        for path in paths:
            if path.is_file():
                chunks = chunk_file(path, content_type)
                all_chunks.extend(chunks)
        print(f'  {name}: {len(paths)} files')
    print(f'Total chunks: {len(all_chunks)}')
    return all_chunks


# --- Embedding ---

def _embed_batch(client: genai.Client, texts: list[str],
                 batch_size: int = 100) -> list[list[float]]:
    """Embed texts in batches using Gemini."""
    all_embeddings = []
    for i in range(0, len(texts), batch_size):
        batch = texts[i:i + batch_size]
        result = client.models.embed_content(
            model=config.EMBEDDING_MODEL,
            contents=batch,
        )
        all_embeddings.extend([e.values for e in result.embeddings])
        print(f'  Embedded {min(i + batch_size, len(texts))}/{len(texts)}')
    return all_embeddings


def _chunk_id(chunk: dict, index: int) -> str:
    """Deterministic ID for a chunk, disambiguated by position."""
    key = f"{chunk['metadata']['source_file']}::{chunk['metadata']['section_heading']}::{index}"
    return hashlib.md5(key.encode()).hexdigest()


# --- Main ---

def build_index(force: bool = False):
    """Build the ChromaDB index from the LRT corpus."""
    print('Gathering chunks...')
    chunks = gather_all_chunks()

    if not chunks:
        print('No chunks found. Check CONTENT_SOURCES paths.')
        return

    # Initialize ChromaDB
    config.CHROMA_PERSIST_DIR.mkdir(parents=True, exist_ok=True)
    client_db = chromadb.PersistentClient(path=str(config.CHROMA_PERSIST_DIR))

    if force:
        try:
            client_db.delete_collection(config.COLLECTION_NAME)
            print('Deleted existing collection.')
        except Exception:
            pass

    collection = client_db.get_or_create_collection(
        name=config.COLLECTION_NAME,
        metadata={'hnsw:space': 'cosine'},
    )

    # Check if already populated
    if collection.count() > 0 and not force:
        print(f'Collection already has {collection.count()} items. Use --force to rebuild.')
        return

    # Embed
    print('Embedding chunks with Gemini...')
    gemini = genai.Client(api_key=config.GEMINI_API_KEY)
    texts = [c['text'] for c in chunks]
    embeddings = _embed_batch(gemini, texts)

    # Store
    print('Storing in ChromaDB...')
    ids = [_chunk_id(c, i) for i, c in enumerate(chunks)]
    metadatas = [c['metadata'] for c in chunks]

    # ChromaDB has a batch limit, insert in groups
    batch = 500
    for i in range(0, len(chunks), batch):
        collection.add(
            ids=ids[i:i + batch],
            embeddings=embeddings[i:i + batch],
            documents=texts[i:i + batch],
            metadatas=metadatas[i:i + batch],
        )

    print(f'Index built: {collection.count()} chunks stored.')


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Build LRT chatbot index')
    parser.add_argument('--force', action='store_true', help='Rebuild from scratch')
    args = parser.parse_args()
    build_index(force=args.force)
