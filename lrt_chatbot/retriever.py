"""LRT retrieval pipeline.

Embeds a user query, searches ChromaDB, and enriches results
with traceability claim data.
"""

import chromadb
from google import genai

from . import config
from .claims import ClaimRegistry


class Retriever:
    """Query the LRT corpus and return enriched context."""

    def __init__(self):
        self._gemini = genai.Client(api_key=config.GEMINI_API_KEY)
        self._db = chromadb.PersistentClient(path=str(config.CHROMA_PERSIST_DIR))
        self._collection = self._db.get_collection(name=config.COLLECTION_NAME)
        self._claims = ClaimRegistry()

    def query(self, text: str, top_k: int = None) -> list[dict]:
        """Retrieve top-k chunks relevant to the query.

        Returns list of dicts with keys:
            text, source_file, section_heading, content_type,
            referenced_claims, claim_details, distance
        """
        k = top_k or config.TOP_K

        # Embed query
        result = self._gemini.models.embed_content(
            model=config.EMBEDDING_MODEL,
            contents=[text],
        )
        query_embedding = result.embeddings[0].values

        # Search
        hits = self._collection.query(
            query_embeddings=[query_embedding],
            n_results=k,
            include=['documents', 'metadatas', 'distances'],
        )

        # Check for direct claim ID mentions in query
        direct_ids = self._claims.extract_claim_ids(text)

        # Build enriched results
        results = []
        seen_claims = set()

        for i in range(len(hits['ids'][0])):
            doc = hits['documents'][0][i]
            meta = hits['metadatas'][0][i]
            dist = hits['distances'][0][i]

            # Collect referenced claim IDs from chunk + dependencies
            ref_str = meta.get('referenced_claims', '')
            ref_ids = [r for r in ref_str.split(',') if r]
            all_claim_ids = set(ref_ids)

            # Add dependency claims for richer context
            for cid in list(all_claim_ids):
                all_claim_ids.update(self._claims.get_dependencies(cid))

            # Format claim details
            claim_details = []
            for cid in sorted(all_claim_ids):
                if cid not in seen_claims:
                    claim = self._claims.get(cid)
                    if claim:
                        claim_details.append({
                            'id': cid,
                            'citation': self._claims.format_citation(cid),
                            'statement': claim.get('statement', '').strip(),
                        })
                        seen_claims.add(cid)

            results.append({
                'text': doc,
                'source_file': meta.get('source_file', ''),
                'section_heading': meta.get('section_heading', ''),
                'content_type': meta.get('content_type', ''),
                'referenced_claims': ref_ids,
                'claim_details': claim_details,
                'distance': dist,
            })

        # If query mentions specific claim IDs not already in results,
        # inject them as additional context
        for cid in direct_ids:
            if cid not in seen_claims:
                claim = self._claims.get(cid)
                if claim:
                    results.append({
                        'text': f"Claim {cid}: {claim.get('statement', '').strip()}",
                        'source_file': f'traceability/claims/{cid}.yaml',
                        'section_heading': cid,
                        'content_type': 'claim_direct',
                        'referenced_claims': [cid],
                        'claim_details': [{
                            'id': cid,
                            'citation': self._claims.format_citation(cid),
                            'statement': claim.get('statement', '').strip(),
                        }],
                        'distance': 0.0,
                    })

        return results

    def get_standing_context(self) -> str:
        """Return the standing context block for prompt assembly."""
        return self._claims.format_chain_summary()
