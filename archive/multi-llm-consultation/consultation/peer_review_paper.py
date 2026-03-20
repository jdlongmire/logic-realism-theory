#!/usr/bin/env python3
"""
Multi-LLM Peer Review Script for Logic Field Theory Paper
Queries Grok-3, GPT-4, and Gemini-2.0 for expert peer review
"""

import asyncio
import json
import sys
from claude_llm_bridge import MultiLLMBridge

async def main():
    print("="*70)
    print("MULTI-LLM PEER REVIEW: Logic Field Theory Paper")
    print("="*70)
    print()

    # Initialize bridge
    bridge = MultiLLMBridge(config_path="./api_config.json")

    # Peer review prompt
    prompt = """
Please provide an expert peer review of the theoretical physics paper:

**Title**: "From 'It from Bit' to 'It from Logic': A Formally Verified Information-Theoretic Foundation for Physical Reality"

**Author**: James D. Longmire

**Key Claims**:
1. Physical reality emerges from logical constraint processing within the Infinite Information Probability Space (I2PS)
2. Central equation: A = L(I) - Actuality = Logical operator acting on I2PS
3. Born rule derived from constraint counting (not postulated)
4. 3+1 spacetime emerges from N=4 permutohedron geometry
5. ~35% formal verification in Lean 4 (with roadmap to 100%)
6. Multi-LLM AI architecture for theorem proving
7. Testable predictions: quantum circuit depths, Bell violations, decoherence scaling

**Focus your review on**:

1. **Theoretical Soundness**: Are the core mathematical claims rigorous? Logical gaps?
2. **Novelty**: What genuinely distinguishes this from standard QM, Many-Worlds, Bohmian mechanics?
3. **Born Rule Derivation**: Is deriving (not postulating) the Born rule from constraints credible?
4. **Spacetime Emergence**: Is the N=4 → 3+1 dimensional claim well-supported?
5. **Experimental Testability**: Are predictions falsifiable and distinguishable from standard QM?
6. **Formal Verification**: Is 35% Lean 4 verification meaningful? Too little? About right for this stage?
7. **Multi-LLM Methodology**: Is AI-assisted theorem proving a genuine contribution or overhyped?
8. **Weaknesses**: What are the main vulnerabilities or areas needing strengthening?
9. **Comparison**: How does this stack up against other foundational approaches?
10. **Recommendation**: Accept, revise, or reject for a top physics journal?

Provide a balanced, expert-level review as if for Physical Review X or Nature Physics.
"""

    print("Querying multi-LLM team for peer review...")
    print("Models: Grok-3, GPT-4, Gemini-2.0-flash-exp")
    print()

    # Run parallel consultation
    results = await bridge.consult_all_experts(prompt)

    # Display results
    print("\n" + "="*70)
    print("PEER REVIEW RESULTS")
    print("="*70)

    # results is a list of dicts
    for response_data in results:
        source = response_data.get('source', 'unknown')
        print(f"\n{'='*70}")
        print(f"MODEL: {source.upper()}")
        print(f"{'='*70}")

        if response_data.get('success'):
            content = response_data.get('content', '')
            try:
                print(content)
            except UnicodeEncodeError:
                # Handle Windows console encoding issues
                print(content.encode('ascii', errors='replace').decode('ascii'))
        else:
            error_msg = response_data.get('error', 'Unknown error')
            try:
                print(f"ERROR: {error_msg}")
            except UnicodeEncodeError:
                print(f"ERROR: {error_msg.encode('ascii', errors='replace').decode('ascii')}")
        print()

    # Save results
    output_file = "../paper/peer_review_multiLLM.json"
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)

    print("="*70)
    print(f"Full results saved to: {output_file}")
    print("="*70)

    # Generate summary
    print("\nGENERATING CONSENSUS SUMMARY...")

    successful_reviews = [r for r in results if r.get('success')]

    if len(successful_reviews) >= 2:
        print(f"\nReceived {len(successful_reviews)}/{len(results)} successful reviews")
        print("\nKEY THEMES ACROSS REVIEWS:")
        print("- Check individual model responses above for detailed critiques")
        print("- Cross-reference points of agreement and disagreement")
        print("- Use consensus insights for paper revision")
    else:
        print(f"\nWARNING: Only {len(successful_reviews)} successful reviews")
        print("Consider checking API keys and connectivity")

    print("\nPeer review complete!")

if __name__ == "__main__":
    asyncio.run(main())
