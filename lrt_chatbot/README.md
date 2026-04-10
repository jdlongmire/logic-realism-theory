# LRT Chatbot

RAG-powered chatbot for Logic Realism Theory. Uses Gemini for embeddings and generation, ChromaDB for vector storage.

## Two Modes

- **Exposition** (default): Neutral, third-person explanation of LRT claims and derivations. Cites claim IDs and epistemic/proof status.
- **Advocacy**: Argues from within the LRT framework. Still honest about open problems, but frames the theory as a coherent research program.

## Setup

```bash
cd lrt-chatbot
pip install -r requirements.txt
cp .env.example .env
# Edit .env with your Gemini API key
```

## Usage

```bash
# 1. Build the index (first time, or after repo changes)
python -m lrt_chatbot.indexer --force

# 2. Run the chatbot
python -m lrt_chatbot
```

Opens at http://localhost:7860

## What Gets Indexed

| Source | Content |
|--------|---------|
| `theory/*.md` | Core theory documents (TAB, MASTER, Cosmology, Formalization) |
| `theory/supplementary/*.md` | Technical supplements (S1-S14) |
| `traceability/claims/*.yaml` | 43 structured claims with epistemic/proof status |
| `docs/formalization/*.md` | Research docs, reviews, analyses |
| `formalization/LrtFormalization/**/*.lean` | Lean4 proofs |

## Architecture

```
User query
    |
    v
Gemini text-embedding-004 --> ChromaDB similarity search
    |
    v
Top-k chunks + standing context (derivation chain) + mode prompt
    |
    v
Gemini 2.5 Pro --> response with claim citations
```

The traceability system is the differentiator: every claim has an ID, epistemic status, proof status, and dependency chain. The chatbot uses these to ground its responses.

## Rebuilding the Index

After making changes to theory files, claims, or Lean code:

```bash
python -m lrt_chatbot.indexer --force
```
