#!/usr/bin/env python3
"""
LRT Traceability Build Script
Generates reports and dependency graphs from claim YAML files.

Usage:
    python build.py [--json] [--graph] [--coverage] [--all]
"""

import os
import sys
import json
import yaml
import argparse
from pathlib import Path
from typing import Dict, List, Any
from collections import defaultdict

SCRIPT_DIR = Path(__file__).parent
CLAIMS_DIR = SCRIPT_DIR.parent / "claims"
GENERATED_DIR = SCRIPT_DIR.parent / "generated"
SCHEMAS_DIR = SCRIPT_DIR.parent / "schemas"


def load_claims() -> Dict[str, Any]:
    """Load all claim YAML files."""
    claims = {}
    for yaml_file in CLAIMS_DIR.glob("*.yaml"):
        with open(yaml_file) as f:
            claim = yaml.safe_load(f)
            if claim and 'id' in claim:
                claims[claim['id']] = claim
    return claims


def generate_json(claims: Dict[str, Any]) -> None:
    """Generate claims.json export."""
    output = {
        "version": "1.0.0",
        "generated": "2026-03-16",
        "claims": claims
    }
    output_path = GENERATED_DIR / "claims.json"
    with open(output_path, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"Generated: {output_path}")


def generate_dependency_graph(claims: Dict[str, Any]) -> None:
    """Generate dependency-graph.json and Mermaid diagram."""
    nodes = []
    edges = []

    for claim_id, claim in claims.items():
        nodes.append({
            "id": claim_id,
            "name": claim.get("name", ""),
            "role": claim.get("role", ""),
            "proof_status": claim.get("proof_status", "")
        })

        for dep in claim.get("depends_on", []):
            if isinstance(dep, dict):
                edges.append({
                    "from": dep["claim_id"],
                    "to": claim_id,
                    "type": dep.get("dependency_type", "logical")
                })
            else:
                edges.append({
                    "from": dep,
                    "to": claim_id,
                    "type": "logical"
                })

    graph = {"nodes": nodes, "edges": edges}

    # JSON output
    json_path = GENERATED_DIR / "dependency-graph.json"
    with open(json_path, 'w') as f:
        json.dump(graph, f, indent=2)
    print(f"Generated: {json_path}")

    # Mermaid output
    mermaid_lines = ["graph TD"]

    # Style definitions
    mermaid_lines.append("    classDef primitive fill:#e1f5fe")
    mermaid_lines.append("    classDef bridge fill:#fff3e0")
    mermaid_lines.append("    classDef derived fill:#e8f5e9")
    mermaid_lines.append("    classDef imported fill:#f3e5f5")
    mermaid_lines.append("    classDef open fill:#ffebee")
    mermaid_lines.append("    classDef prediction fill:#e0f2f1")

    for node in nodes:
        label = node["name"][:30] + "..." if len(node["name"]) > 30 else node["name"]
        mermaid_lines.append(f'    {node["id"]}["{node["id"]}: {label}"]')

    for edge in edges:
        style = "-->" if edge["type"] == "logical" else "-.->|{0}|".format(edge["type"])
        mermaid_lines.append(f'    {edge["from"]} {style} {edge["to"]}')

    # Apply styles
    for node in nodes:
        role = node.get("role", "derived")
        mermaid_lines.append(f'    class {node["id"]} {role}')

    mermaid_path = GENERATED_DIR / "dependency-graph.mmd"
    with open(mermaid_path, 'w') as f:
        f.write("\n".join(mermaid_lines))
    print(f"Generated: {mermaid_path}")


def generate_coverage_report(claims: Dict[str, Any]) -> None:
    """Generate coverage-report.md."""
    lines = ["# LRT Claim Coverage Report", "", f"Generated: 2026-03-16", ""]

    # Summary table
    status_counts = defaultdict(int)
    role_counts = defaultdict(int)
    epistemic_counts = defaultdict(int)

    for claim in claims.values():
        status_counts[claim.get("proof_status", "unknown")] += 1
        role_counts[claim.get("role", "unknown")] += 1
        epistemic_counts[claim.get("epistemic_status", "unknown")] += 1

    lines.append("## Summary")
    lines.append("")
    lines.append(f"**Total claims:** {len(claims)}")
    lines.append("")

    lines.append("### By Proof Status")
    lines.append("")
    lines.append("| Status | Count |")
    lines.append("|--------|-------|")
    for status, count in sorted(status_counts.items()):
        lines.append(f"| {status} | {count} |")
    lines.append("")

    lines.append("### By Role")
    lines.append("")
    lines.append("| Role | Count |")
    lines.append("|------|-------|")
    for role, count in sorted(role_counts.items()):
        lines.append(f"| {role} | {count} |")
    lines.append("")

    lines.append("### By Epistemic Status")
    lines.append("")
    lines.append("| Status | Count |")
    lines.append("|--------|-------|")
    for status, count in sorted(epistemic_counts.items()):
        lines.append(f"| {status} | {count} |")
    lines.append("")

    # Detailed listing
    lines.append("## Claim Details")
    lines.append("")

    for claim_id in sorted(claims.keys()):
        claim = claims[claim_id]
        lines.append(f"### {claim_id}: {claim.get('name', 'Unnamed')}")
        lines.append("")
        lines.append(f"- **Role:** {claim.get('role', 'unknown')}")
        lines.append(f"- **Proof status:** {claim.get('proof_status', 'unknown')}")
        lines.append(f"- **Epistemic status:** {claim.get('epistemic_status', 'unknown')}")

        deps = claim.get("depends_on", [])
        if deps:
            dep_ids = [d["claim_id"] if isinstance(d, dict) else d for d in deps]
            lines.append(f"- **Depends on:** {', '.join(dep_ids)}")

        artifacts = claim.get("formal_artifacts", {}).get("lean", [])
        if artifacts:
            lines.append(f"- **Lean artifacts:** {len(artifacts)} symbols")

        lines.append("")

    output_path = GENERATED_DIR / "coverage-report.md"
    with open(output_path, 'w') as f:
        f.write("\n".join(lines))
    print(f"Generated: {output_path}")


def generate_risk_report(claims: Dict[str, Any]) -> None:
    """Generate risk-report.md highlighting choke points."""
    lines = ["# LRT Risk Assessment Report", "", f"Generated: 2026-03-16", ""]

    # Find bridge principles (high risk)
    bridges = [c for c in claims.values() if c.get("role") == "bridge"]

    # Find axiomatized claims
    axiomatized = [c for c in claims.values() if c.get("proof_status") == "axiomatized"]

    # Find open problems
    open_problems = [c for c in claims.values() if c.get("role") == "open"]

    lines.append("## High-Risk Choke Points")
    lines.append("")
    lines.append("These claims are bridge principles: philosophically argued but not logically forced.")
    lines.append("")

    for claim in bridges:
        lines.append(f"### {claim['id']}: {claim.get('name', '')}")
        lines.append("")
        lines.append(f"> {claim.get('statement', '')[:200]}...")
        lines.append("")
        lines.append(f"**Risk if false:** {claim.get('risk_if_false', 'Not specified')}")
        lines.append("")

    lines.append("## Axiomatized Claims (Not Yet Verified)")
    lines.append("")
    lines.append("These claims are implemented in Lean but use `axiom` or `sorry`.")
    lines.append("")

    for claim in axiomatized:
        if claim.get("role") != "bridge":  # Don't double-list
            lines.append(f"- **{claim['id']}**: {claim.get('name', '')}")
    lines.append("")

    lines.append("## Open Problems")
    lines.append("")

    for claim in open_problems:
        lines.append(f"### {claim['id']}: {claim.get('name', '')}")
        lines.append("")
        lines.append(claim.get('statement', ''))
        lines.append("")

    output_path = GENERATED_DIR / "risk-report.md"
    with open(output_path, 'w') as f:
        f.write("\n".join(lines))
    print(f"Generated: {output_path}")


def main():
    parser = argparse.ArgumentParser(description="LRT Traceability Build Script")
    parser.add_argument("--json", action="store_true", help="Generate claims.json")
    parser.add_argument("--graph", action="store_true", help="Generate dependency graph")
    parser.add_argument("--coverage", action="store_true", help="Generate coverage report")
    parser.add_argument("--risk", action="store_true", help="Generate risk report")
    parser.add_argument("--all", action="store_true", help="Generate all outputs")

    args = parser.parse_args()

    # Default to --all if no options specified
    if not any([args.json, args.graph, args.coverage, args.risk, args.all]):
        args.all = True

    # Ensure output directory exists
    GENERATED_DIR.mkdir(exist_ok=True)

    # Load claims
    claims = load_claims()
    print(f"Loaded {len(claims)} claims")

    if args.json or args.all:
        generate_json(claims)

    if args.graph or args.all:
        generate_dependency_graph(claims)

    if args.coverage or args.all:
        generate_coverage_report(claims)

    if args.risk or args.all:
        generate_risk_report(claims)

    print("\nBuild complete.")


if __name__ == "__main__":
    main()
