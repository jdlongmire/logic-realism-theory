#!/usr/bin/env python3
"""
Citation Verification Script (v1.0.0)

Queries Crossref API to get authoritative bibliographic data for a DOI.
Part of reference_validation_protocol/reference_validation_protocol.json v0.2.3

Usage:
    python verify_citation.py <DOI>
    python verify_citation.py --file <citations.txt>
    python verify_citation.py --compare "<provided citation>" <DOI>

Examples:
    python verify_citation.py 10.1103/PhysRevLett.102.020505
    python verify_citation.py --compare "McKague, M. QIC 9, 2009: 1158" 10.1103/PhysRevLett.102.020505
"""

import argparse
import json
import sys
import urllib.request
import urllib.error
from typing import Optional
from dataclasses import dataclass, asdict
from datetime import datetime, timezone


@dataclass
class CitationData:
    """Authoritative citation data from Crossref."""
    doi: str
    title: str
    authors: list[str]
    journal: str
    volume: Optional[str]
    issue: Optional[str]
    pages: Optional[str]
    article_number: Optional[str]
    year: int
    publisher: str
    url: str
    source: str = "crossref_api"
    accessed_at: str = ""

    def __post_init__(self):
        if not self.accessed_at:
            self.accessed_at = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")

    def to_formatted_citation(self) -> str:
        """Format as a standard citation string."""
        # Authors
        if len(self.authors) == 1:
            author_str = self.authors[0]
        elif len(self.authors) == 2:
            author_str = f"{self.authors[0]} and {self.authors[1]}"
        elif len(self.authors) > 2:
            author_str = f"{self.authors[0]} et al."
        else:
            author_str = "[No authors]"

        # Volume/pages
        vol_str = ""
        if self.volume:
            vol_str = f" {self.volume}"
            if self.issue:
                vol_str += f"({self.issue})"

        page_str = ""
        if self.pages:
            page_str = f": {self.pages}"
        elif self.article_number:
            page_str = f": {self.article_number}"

        return f'{author_str}. "{self.title}" *{self.journal}*{vol_str}, {self.year}{page_str}.'

    def to_json(self) -> str:
        """Export as JSON for protocol compliance."""
        return json.dumps(asdict(self), indent=2)


def query_crossref(doi: str) -> Optional[CitationData]:
    """
    Query Crossref API for DOI metadata.

    This is a tier_1 authoritative source per reference_validation_protocol.json v0.2.3.
    """
    # Clean DOI
    doi = doi.strip()
    if doi.startswith("https://doi.org/"):
        doi = doi[16:]
    elif doi.startswith("http://doi.org/"):
        doi = doi[15:]
    elif doi.startswith("doi:"):
        doi = doi[4:]

    url = f"https://api.crossref.org/works/{doi}"

    # Crossref asks for a User-Agent with contact info
    headers = {
        "User-Agent": "LRT-Citation-Verifier/1.0 (mailto:jdlongmire@outlook.com)",
        "Accept": "application/json"
    }

    try:
        request = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(request, timeout=30) as response:
            data = json.loads(response.read().decode())
    except urllib.error.HTTPError as e:
        if e.code == 404:
            print(f"ERROR: DOI not found in Crossref: {doi}", file=sys.stderr)
        else:
            print(f"ERROR: HTTP {e.code} from Crossref API", file=sys.stderr)
        return None
    except urllib.error.URLError as e:
        print(f"ERROR: Network error: {e.reason}", file=sys.stderr)
        return None
    except json.JSONDecodeError:
        print("ERROR: Invalid JSON response from Crossref", file=sys.stderr)
        return None

    # Parse response
    msg = data.get("message", {})

    # Extract authors
    authors = []
    for author in msg.get("author", []):
        given = author.get("given", "")
        family = author.get("family", "")
        if given and family:
            authors.append(f"{family}, {given[0]}.")
        elif family:
            authors.append(family)

    # Extract title
    titles = msg.get("title", [])
    title = titles[0] if titles else "[No title]"

    # Extract journal
    containers = msg.get("container-title", [])
    journal = containers[0] if containers else "[No journal]"

    # Extract volume/issue/pages
    volume = msg.get("volume")
    issue = msg.get("issue")
    pages = msg.get("page")
    article_number = msg.get("article-number")

    # Extract year
    published = msg.get("published", {})
    date_parts = published.get("date-parts", [[None]])
    year = date_parts[0][0] if date_parts and date_parts[0] else None

    # Fallback to other date fields
    if not year:
        for date_field in ["published-print", "published-online", "created"]:
            if date_field in msg:
                date_parts = msg[date_field].get("date-parts", [[None]])
                if date_parts and date_parts[0]:
                    year = date_parts[0][0]
                    break

    # Publisher
    publisher = msg.get("publisher", "[Unknown publisher]")

    # DOI URL
    doi_url = f"https://doi.org/{doi}"

    return CitationData(
        doi=doi,
        title=title,
        authors=authors,
        journal=journal,
        volume=volume,
        issue=issue,
        pages=pages,
        article_number=article_number,
        year=year or 0,
        publisher=publisher,
        url=doi_url
    )


def compare_citation(provided: str, authoritative: CitationData) -> dict:
    """
    Compare a provided citation against authoritative data.

    Returns a dict with comparison results.
    """
    results = {
        "provided": provided,
        "authoritative": authoritative.to_formatted_citation(),
        "doi": authoritative.doi,
        "discrepancies": [],
        "warnings": []
    }

    provided_lower = provided.lower()

    # Check journal
    journal_lower = authoritative.journal.lower()
    # Common abbreviations
    journal_variants = [
        journal_lower,
        journal_lower.replace("physical review letters", "prl"),
        journal_lower.replace("new journal of physics", "njp"),
        journal_lower.replace("physical review ", "phys. rev. "),
    ]

    journal_found = any(v in provided_lower for v in journal_variants)
    if not journal_found:
        results["discrepancies"].append({
            "field": "journal",
            "expected": authoritative.journal,
            "note": "Journal name not found in provided citation"
        })

    # Check year
    if authoritative.year and str(authoritative.year) not in provided:
        results["discrepancies"].append({
            "field": "year",
            "expected": authoritative.year,
            "note": f"Year {authoritative.year} not found in provided citation"
        })

    # Check volume
    if authoritative.volume and authoritative.volume not in provided:
        results["warnings"].append({
            "field": "volume",
            "expected": authoritative.volume,
            "note": "Volume may not match"
        })

    # Check article number / pages
    if authoritative.article_number and authoritative.article_number not in provided:
        if authoritative.pages and authoritative.pages not in provided:
            results["warnings"].append({
                "field": "pages/article",
                "expected": authoritative.article_number or authoritative.pages,
                "note": "Pages/article number may not match"
            })

    results["status"] = "MATCH" if not results["discrepancies"] else "DISCREPANCY"

    return results


def print_citation_data(data: CitationData, output_format: str = "text"):
    """Print citation data in requested format."""
    if output_format == "json":
        print(data.to_json())
    else:
        print("=" * 70)
        print("AUTHORITATIVE CITATION DATA (from Crossref API - tier_1 source)")
        print("=" * 70)
        print(f"DOI:      {data.doi}")
        print(f"URL:      {data.url}")
        print(f"Accessed: {data.accessed_at}")
        print("-" * 70)
        print(f"Title:    {data.title}")
        print(f"Authors:  {', '.join(data.authors)}")
        print(f"Journal:  {data.journal}")
        print(f"Year:     {data.year}")
        if data.volume:
            vol_str = data.volume
            if data.issue:
                vol_str += f"({data.issue})"
            print(f"Volume:   {vol_str}")
        if data.pages:
            print(f"Pages:    {data.pages}")
        if data.article_number:
            print(f"Article:  {data.article_number}")
        print(f"Publisher: {data.publisher}")
        print("-" * 70)
        print("FORMATTED CITATION:")
        print(data.to_formatted_citation())
        print("=" * 70)


def main():
    parser = argparse.ArgumentParser(
        description="Verify citations using Crossref API (tier_1 source)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument("doi", nargs="?", help="DOI to look up")
    parser.add_argument("--compare", "-c", metavar="CITATION",
                        help="Compare provided citation against DOI data")
    parser.add_argument("--file", "-f", metavar="FILE",
                        help="File containing DOIs (one per line)")
    parser.add_argument("--json", "-j", action="store_true",
                        help="Output in JSON format")

    args = parser.parse_args()

    if not args.doi and not args.file:
        parser.print_help()
        sys.exit(1)

    output_format = "json" if args.json else "text"

    # Process single DOI
    if args.doi:
        data = query_crossref(args.doi)
        if not data:
            sys.exit(1)

        if args.compare:
            results = compare_citation(args.compare, data)
            if output_format == "json":
                print(json.dumps(results, indent=2))
            else:
                print("\n" + "=" * 70)
                print("COMPARISON RESULTS")
                print("=" * 70)
                print(f"PROVIDED:      {results['provided']}")
                print(f"AUTHORITATIVE: {results['authoritative']}")
                print(f"STATUS:        {results['status']}")
                if results["discrepancies"]:
                    print("\nDISCREPANCIES (likely errors):")
                    for d in results["discrepancies"]:
                        print(f"  - {d['field']}: expected '{d['expected']}' - {d['note']}")
                if results["warnings"]:
                    print("\nWARNINGS (check manually):")
                    for w in results["warnings"]:
                        print(f"  - {w['field']}: expected '{w['expected']}' - {w['note']}")
                print("=" * 70)
        else:
            print_citation_data(data, output_format)

    # Process file of DOIs
    elif args.file:
        try:
            with open(args.file, 'r') as f:
                dois = [line.strip() for line in f if line.strip() and not line.startswith('#')]
        except FileNotFoundError:
            print(f"ERROR: File not found: {args.file}", file=sys.stderr)
            sys.exit(1)

        results = []
        for doi in dois:
            data = query_crossref(doi)
            if data:
                if output_format == "json":
                    results.append(asdict(data))
                else:
                    print_citation_data(data, output_format)
                    print()

        if output_format == "json":
            print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
