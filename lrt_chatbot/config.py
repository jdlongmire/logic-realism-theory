"""LRT Chatbot configuration."""

import os
from pathlib import Path

from dotenv import load_dotenv

# Load .env from chatbot directory, then repo root
_chatbot_dir = Path(__file__).parent
load_dotenv(_chatbot_dir / '.env')
load_dotenv(_chatbot_dir.parent / '.env')

# --- API ---
GEMINI_API_KEY = os.getenv('GEMINI_API_KEY')
EMBEDDING_MODEL = os.getenv('LRT_EMBEDDING_MODEL', 'gemini-embedding-001')
LLM_MODEL = os.getenv('LRT_LLM_MODEL', 'gemini-2.5-pro')
LLM_FALLBACK_MODEL = os.getenv('LRT_LLM_FALLBACK', 'gemini-2.0-flash')

# --- Paths ---
LRT_REPO_ROOT = _chatbot_dir.parent
CHROMA_PERSIST_DIR = _chatbot_dir / 'chroma_db'
THEORY_DIR = LRT_REPO_ROOT / 'theory'
SUPPLEMENTARY_DIR = THEORY_DIR / 'supplementary'
TRACEABILITY_DIR = LRT_REPO_ROOT / 'traceability'
CLAIMS_DIR = TRACEABILITY_DIR / 'claims'
FORMALIZATION_DOCS_DIR = LRT_REPO_ROOT / 'docs' / 'formalization'
LEAN_DIR = LRT_REPO_ROOT / 'formalization' / 'LrtFormalization'

# --- Indexing ---
CHUNK_SIZE = 800       # tokens (approx chars / 4)
CHUNK_OVERLAP = 100
COLLECTION_NAME = 'lrt_corpus'

# --- Retrieval ---
TOP_K = 8

# Content sources: (name, glob pattern relative to repo root, content_type tag)
CONTENT_SOURCES = [
    ('theory', 'theory/*.md', 'theory'),
    ('supplementary', 'theory/supplementary/*.md', 'supplementary'),
    ('claims', 'traceability/claims/*.yaml', 'claim'),
    ('formalization_docs', 'docs/formalization/*.md', 'formalization_doc'),
    ('lean', 'formalization/LrtFormalization/**/*.lean', 'lean'),
]
