#!/usr/bin/env python3
"""
Multi-LLM Consultation: Spacetime Scaling Analysis Review

Consults Grok-3, GPT-4, and Gemini-2.0 on the spacetime scaling analysis
from Session 4.0, requesting expert feedback on:

1. Dimension estimation methodology (correlation dimension vs alternatives)
2. Non-monotonic convergence interpretation (1.00 -> 3.16 -> 2.38 -> 2.69)
3. Continuum limit strategy (computational vs analytical vs hybrid)
4. Symmetry group analysis (why automorphisms are so small)
5. Literature comparison (positioning vs existing approaches)
6. Publication strategy (ready for Paper II or need more validation)

Session 4.0 Status: N=3-6 scaling complete, dimension ~ 3 validated but non-monotonic.
"""

import asyncio
import json
import os
import sys
from datetime import datetime
from pathlib import Path

# Add current directory to path for imports
sys.path.append(str(Path(__file__).parent))

try:
    from claude_llm_bridge import MultiLLMBridge
except ImportError:
    print("Error: claude_llm_bridge.py not found. Make sure you're in the multi_LLM directory.")
    sys.exit(1)


def load_spacetime_query():
    """Load the spacetime scaling analysis query"""
    query_file = Path(__file__).parent / "spacetime_scaling_query.md"
    if not query_file.exists():
        raise FileNotFoundError(f"Spacetime query file not found: {query_file}")

    with open(query_file, 'r', encoding='utf-8') as f:
        return f.read()


async def consult_on_spacetime_scaling():
    """Run multi-LLM consultation on spacetime scaling analysis"""

    print("=" * 80)
    print("SPACETIME SCALING ANALYSIS - MULTI-LLM EXPERT CONSULTATION")
    print("=" * 80)
    print()
    print("CONTEXT: Session 4.0 - N=3,4,5,6 scaling analysis COMPLETE")
    print("         Spatial dimension: N=4 (3.16), N=6 (2.69) - approaching 3D")
    print("         Metric signature: 100% validated (all spatial intervals spacelike)")
    print("         Symmetry groups: Discrete Poincare-like (G_N ~ S_N x R) for N>=5")
    print()
    print("QUESTIONS: 6 expert review questions on methodology, interpretation, strategy")
    print()

    # Load spacetime query
    try:
        query = load_spacetime_query()
        print(f"Loaded spacetime scaling query ({len(query)} characters)")
    except FileNotFoundError as e:
        print(f"Error: {e}")
        return

    # Check API configuration
    config_file = Path(__file__).parent / "api_config.json"
    if not config_file.exists():
        print()
        print("ERROR: API configuration not found!")
        print(f"Expected at: {config_file}")
        return

    # Initialize bridge
    bridge = MultiLLMBridge()

    print()
    print("Consulting expert LLMs (this may take 90-120 seconds for comprehensive review)...")
    print()

    # Run consultation
    try:
        results = await bridge.consult_all_experts(query)

        # Extract responses from results (handle both dict and exception results)
        responses = {}
        for i, (model_name, result) in enumerate(zip(['grok', 'chatgpt', 'gemini'], results)):
            if isinstance(result, Exception):
                print(f"[ERROR] {model_name} failed: {result}")
                responses[model_name] = f"Error: {str(result)}"
            elif isinstance(result, dict):
                if result.get('success'):
                    # Success - extract content
                    responses[model_name] = result.get('content', str(result))
                    print(f"[SUCCESS] {model_name} responded ({len(responses[model_name])} chars)")
                else:
                    # Failure - extract error
                    error_msg = result.get('error', 'Unknown error')
                    print(f"[ERROR] {model_name} failed: {error_msg}")
                    responses[model_name] = f"Error: {error_msg}"
            else:
                print(f"[WARNING] {model_name} returned unexpected format: {type(result)}")
                responses[model_name] = str(result)

        # Save individual responses with timestamp
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

        for model, response in responses.items():
            filename = Path(__file__).parent / f"spacetime_scaling_{model}_{timestamp}.md"
            with open(filename, 'w', encoding='utf-8') as f:
                f.write(f"# Spacetime Scaling Analysis Review - {model.upper()}\n\n")
                f.write(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
                f.write(f"**Context**: Session 4.0 - N=3,4,5,6 scaling complete\n\n")
                f.write("**Key Results**:\n")
                f.write("- N=4 dimension: 3.16 (5% above 3D target)\n")
                f.write("- N=6 dimension: 2.69 (10% below 3D target)\n")
                f.write("- Metric signature: 100% validated (spacelike spatial intervals)\n")
                f.write("- Symmetry: Discrete Poincare-like (G_N ~ S_N x R) for N>=5\n")
                f.write("- Non-monotonic convergence: 1.00 -> 3.16 -> 2.38 -> 2.69\n\n")
                f.write("---\n\n")
                f.write(response)

            print(f"[OK] Saved {model} response: {filename.name}")

        # Create synthesis
        print()
        print("Synthesizing expert recommendations...")

        synthesis_lines = []
        synthesis_lines.append("# Spacetime Scaling Analysis - Expert Consensus\n\n")
        synthesis_lines.append(f"**Timestamp**: {datetime.now().isoformat()}\n\n")
        synthesis_lines.append("## Summary of Expert Feedback\n\n")

        for model, response in responses.items():
            synthesis_lines.append(f"### {model.upper()} Key Points:\n\n")
            # Take first 500 chars as summary
            summary = response[:500] + "..." if len(response) > 500 else response
            synthesis_lines.append(summary + "\n\n")

        synthesis = "".join(synthesis_lines)

        # Save synthesis
        synthesis_file = Path(__file__).parent / f"spacetime_scaling_synthesis_{timestamp}.md"
        with open(synthesis_file, 'w', encoding='utf-8') as f:
            f.write(synthesis)

        print(f"[OK] Saved synthesis: {synthesis_file.name}")

        # Print summary
        print()
        print("=" * 80)
        print("CONSULTATION COMPLETE")
        print("=" * 80)
        print()
        print(f"Results saved in multi_LLM directory:")
        print(f"  - Individual responses: spacetime_scaling_{{model}}_{timestamp}.md")
        print(f"  - Synthesis: spacetime_scaling_synthesis_{timestamp}.md")
        print()
        print("Next steps:")
        print("1. Review individual expert opinions on each question")
        print("2. Read synthesis for key consensus points")
        print("3. Decide on methodology adjustments:")
        print("   - Try alternative dimension estimators?")
        print("   - Extend to N=7,8 for more data?")
        print("   - Start analytical continuum limit analysis?")
        print("4. Determine publication timeline:")
        print("   - (A) Paper II now with preliminary scaling results")
        print("   - (B) Wait for continuum limit completion (6-12 months)")
        print("   - (C) Two-paper strategy (metric+symmetries now, continuum later)")
        print()

    except Exception as e:
        print(f"Error during consultation: {e}")
        import traceback
        traceback.print_exc()
        print()
        print("You can still view the query at:")
        print(f"  {Path(__file__).parent / 'spacetime_scaling_query.md'}")


def main():
    """Main entry point"""
    asyncio.run(consult_on_spacetime_scaling())


if __name__ == "__main__":
    main()
