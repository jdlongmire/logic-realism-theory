"""Traceability claim registry for LRT.

Parses YAML claim files and the index to provide structured claim data
for RAG enrichment and citation.
"""

import re
from pathlib import Path

import yaml

from . import config


def _load_yaml(path: Path) -> dict:
    """Load a YAML file, returning empty dict on failure."""
    try:
        with open(path) as f:
            return yaml.safe_load(f) or {}
    except Exception:
        return {}


class ClaimRegistry:
    """Registry of all LRT traceability claims."""

    # Pattern to detect claim IDs in text
    CLAIM_ID_PATTERN = re.compile(
        r'\b(ONT|LOG|ACT|QM|PHY|INT|PRD|OPN|EXT)-\d{3}\b'
    )

    def __init__(self, claims_dir: Path = None, index_path: Path = None):
        self.claims_dir = claims_dir or config.CLAIMS_DIR
        self.index_path = index_path or (config.TRACEABILITY_DIR / 'index.yaml')
        self._claims: dict[str, dict] = {}
        self._index: dict = {}
        self._load()

    def _load(self):
        """Load all claims and the index."""
        # Load index
        self._index = _load_yaml(self.index_path)

        # Load individual claim files
        if self.claims_dir.exists():
            for path in sorted(self.claims_dir.glob('*.yaml')):
                data = _load_yaml(path)
                if 'id' in data:
                    self._claims[data['id']] = data

    def get(self, claim_id: str) -> dict | None:
        """Get a claim by ID."""
        return self._claims.get(claim_id)

    def all_claims(self) -> dict[str, dict]:
        """Return all claims."""
        return dict(self._claims)

    def derivation_chain(self) -> list[str]:
        """Return the ordered derivation chain from the index."""
        return self._index.get('derivation_chain', [])

    def status_summary(self) -> dict:
        """Return the status summary from the index."""
        return self._index.get('status_summary', {})

    def choke_points(self) -> list[dict]:
        """Return critical choke points from the index."""
        return self._index.get('choke_points', [])

    def claims_by_status(self, proof_status: str = None,
                         epistemic_status: str = None) -> list[dict]:
        """Filter claims by proof and/or epistemic status."""
        results = []
        for claim in self._claims.values():
            if proof_status and claim.get('proof_status') != proof_status:
                continue
            if epistemic_status and claim.get('epistemic_status') != epistemic_status:
                continue
            results.append(claim)
        return results

    def format_citation(self, claim_id: str) -> str:
        """Format a compact citation string for a claim."""
        claim = self.get(claim_id)
        if not claim:
            return f'[{claim_id}: unknown]'
        name = claim.get('name', '?')
        ep = claim.get('epistemic_status', '?')
        pf = claim.get('proof_status', '?')
        return f'[{claim_id} | {name} | {ep}/{pf}]'

    def format_chain_summary(self) -> str:
        """Format the derivation chain with status for prompt injection."""
        chain = self.derivation_chain()
        lines = ['LRT Derivation Chain:']
        for cid in chain:
            claim = self.get(cid)
            if claim:
                name = claim.get('name', '?')
                ep = claim.get('epistemic_status', '?')
                pf = claim.get('proof_status', '?')
                lines.append(f'  {cid}: {name} [{ep}/{pf}]')
            else:
                lines.append(f'  {cid}: (not found)')

        summary = self.status_summary()
        if summary:
            lines.append('')
            lines.append(f'Status: {summary.get("total_claims", "?")} claims total')
            for key in ['verified', 'axiomatized', 'derived', 'imported',
                        'prose_only', 'open']:
                if key in summary:
                    lines.append(f'  {key}: {summary[key]}')
        return '\n'.join(lines)

    def extract_claim_ids(self, text: str) -> list[str]:
        """Extract all claim IDs mentioned in a text."""
        return list(set(
            m.group(0) for m in self.CLAIM_ID_PATTERN.finditer(text)
        ))

    def get_dependencies(self, claim_id: str, depth: int = 1) -> list[str]:
        """Get dependency claim IDs, optionally recursive."""
        claim = self.get(claim_id)
        if not claim:
            return []
        deps = [d['claim_id'] for d in claim.get('depends_on', [])]
        if depth > 1:
            for dep_id in list(deps):
                deps.extend(self.get_dependencies(dep_id, depth - 1))
        return list(set(deps))
