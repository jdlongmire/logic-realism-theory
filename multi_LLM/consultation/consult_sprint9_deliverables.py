#!/usr/bin/env python3
"""
Sprint 9 Phase 4: Multi-LLM Team Consultation on Sprint 9 Deliverables
Consults team on Mission Statement, Research Roadmap, and Lean Status Report
"""

import sys
import asyncio
import json
from pathlib import Path
from datetime import datetime

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from enhanced_llm_bridge import EnhancedMultiLLMBridge, QueryType


async def main():
    """Run comprehensive Sprint 9 deliverables review."""
    # Set config path relative to multi_LLM directory
    config_path = str(Path(__file__).parent.parent / "api_config.json")
    bridge = EnhancedMultiLLMBridge(config_path=config_path)

    # Load the three key deliverables
    base_path = Path(__file__).parent.parent.parent

    # Read Mission Statement
    mission_path = base_path / "MISSION_STATEMENT.md"
    with open(mission_path, 'r', encoding='utf-8') as f:
        mission_statement = f.read()

    # Read Research Roadmap
    roadmap_path = base_path / "RESEARCH_ROADMAP.md"
    with open(roadmap_path, 'r', encoding='utf-8') as f:
        research_roadmap = f.read()

    # Read Lean Status Report
    lean_status_path = base_path / "LEAN_STATUS_REPORT.md"
    with open(lean_status_path, 'r', encoding='utf-8') as f:
        lean_status = f.read()

    print("=" * 80)
    print("SPRINT 9 PHASE 4: MULTI-LLM TEAM CONSULTATION")
    print("=" * 80)
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Deliverables: MISSION_STATEMENT.md, RESEARCH_ROADMAP.md, LEAN_STATUS_REPORT.md")
    print(f"Quality Score Target: >0.70")
    print("=" * 80)

    # Consultation 1: Mission Statement Review
    print("\n\n" + "=" * 80)
    print("CONSULTATION 1: MISSION STATEMENT REVIEW")
    print("=" * 80)

    mission_prompt = f"""
SPRINT 9 PHASE 4: MISSION STATEMENT REVIEW

You are a peer reviewer for a theoretical physics research program. Review the following mission statement document and provide constructive feedback.

DOCUMENT: MISSION_STATEMENT.md (~6,400 words)

{mission_statement}

---

REVIEW CRITERIA:
1. **Conceptual Clarity**: Are the core concepts (3FLL, Information Space, Logic Realism Principle) clearly articulated?
2. **Scope Honesty**: Are the limitations and boundaries honestly stated?
3. **Falsification Criteria**: Are the testable predictions and falsification conditions clear and concrete?
4. **Philosophical Justification**: Is the Gödel argument properly positioned (motivating, not proof)?
5. **Integration**: Do the philosophical and technical levels integrate coherently?
6. **Roadmap Alignment**: Does the mission connect clearly to the research roadmap?

PROVIDE:
- **Strengths**: What works well (2-3 points)
- **Weaknesses**: What needs improvement (2-3 points with specific line references if possible)
- **Critical Issues**: Any fundamental problems or contradictions
- **Recommendations**: Concrete suggestions for enhancement
- **Overall Assessment**: Accept / Minor Revision / Major Revision / Reject

Focus on conceptual clarity, scientific honesty, and publication readiness.
"""

    result1 = await bridge.consult_all_experts(mission_prompt, QueryType.PEER_REVIEW)
    bridge.print_results_with_scores(result1)

    best1 = result1.get('best_response')
    quality1 = best1['quality'] if best1 else 0.0

    # Save consultation 1 result
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    output_path1 = base_path / f"multi_LLM/consultation/sprint9_mission_statement_{timestamp}.txt"
    with open(output_path1, 'w', encoding='utf-8') as f:
        f.write(f"Sprint 9 Phase 4 - Mission Statement Review\n")
        f.write(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Quality Score: {quality1:.3f}\n")
        f.write("=" * 80 + "\n\n")
        for resp in result1['responses']:
            if resp.get('success'):
                f.write(f"SOURCE: {resp['source'].upper()}\n")
                f.write(f"Quality: {resp.get('quality_score', 0):.3f}\n")
                f.write("-" * 80 + "\n")
                f.write(resp['content'])
                f.write("\n\n" + "=" * 80 + "\n\n")

    print(f"\nSaved consultation 1 to: {output_path1}")

    # Consultation 2: Research Roadmap Review
    print("\n\n" + "=" * 80)
    print("CONSULTATION 2: RESEARCH ROADMAP REVIEW")
    print("=" * 80)

    roadmap_prompt = f"""
SPRINT 9 PHASE 4: RESEARCH ROADMAP REVIEW

You are a research program reviewer evaluating a 3-year strategic plan for a theoretical physics framework.

DOCUMENT: RESEARCH_ROADMAP.md (~6,400 words)

{research_roadmap}

---

REVIEW CRITERIA:
1. **Timeline Realism**: Are the near-term (Sprints 9-12), medium-term (6-12 months), and long-term (1-3 years) goals achievable?
2. **Critical Decision Points**: Is Sprint 10 (Young diagrams for indistinguishable particles) properly positioned as a pivotal test?
3. **Resource Planning**: Is the personnel/funding plan ($3M over 3 years) realistic for the scope?
4. **Contingency Planning**: Are pivot points and failure modes properly addressed?
5. **Success Metrics**: Are the validation tiers and criteria clear and measurable?
6. **Integration**: Does the roadmap align with the mission statement scope and limitations?

PROVIDE:
- **Strengths**: What works well (2-3 points)
- **Weaknesses**: What needs improvement (2-3 points with specific section references)
- **Critical Issues**: Any unrealistic goals or missing considerations
- **Recommendations**: Concrete suggestions for enhancement
- **Overall Assessment**: Accept / Minor Revision / Major Revision / Reject

Focus on feasibility, scientific honesty, and strategic coherence.
"""

    result2 = await bridge.consult_all_experts(roadmap_prompt, QueryType.PEER_REVIEW)
    bridge.print_results_with_scores(result2)

    best2 = result2.get('best_response')
    quality2 = best2['quality'] if best2 else 0.0

    # Save consultation 2 result
    output_path2 = base_path / f"multi_LLM/consultation/sprint9_research_roadmap_{timestamp}.txt"
    with open(output_path2, 'w', encoding='utf-8') as f:
        f.write(f"Sprint 9 Phase 4 - Research Roadmap Review\n")
        f.write(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Quality Score: {quality2:.3f}\n")
        f.write("=" * 80 + "\n\n")
        for resp in result2['responses']:
            if resp.get('success'):
                f.write(f"SOURCE: {resp['source'].upper()}\n")
                f.write(f"Quality: {resp.get('quality_score', 0):.3f}\n")
                f.write("-" * 80 + "\n")
                f.write(resp['content'])
                f.write("\n\n" + "=" * 80 + "\n\n")

    print(f"\nSaved consultation 2 to: {output_path2}")

    # Consultation 3: Lean Status Report Review
    print("\n\n" + "=" * 80)
    print("CONSULTATION 3: LEAN STATUS REPORT REVIEW")
    print("=" * 80)

    lean_prompt = f"""
SPRINT 9 PHASE 4: LEAN STATUS REPORT REVIEW

You are a formal verification expert reviewing a comprehensive audit of a Lean 4 formalization for quantum mechanics derivation.

DOCUMENT: LEAN_STATUS_REPORT.md (~10,500 words)

{lean_status}

---

REVIEW CRITERIA:
1. **Audit Completeness**: Does the report cover all 17 modules systematically?
2. **Axiom Justification**: Are the 126 strategic axioms properly categorized and justified?
3. **Confidence Assessment**: Is the 87% overall confidence rating defensible?
4. **Roadmap**: Is the plan to reduce 126 axioms → ~90-100 (Sprints 11-12) → <50 (long-term) realistic?
5. **Critical Analysis**: Does the report identify MeasurementMechanism.lean (20/126 axioms) as the primary target?
6. **Notebook Correspondence**: Is the 61% notebook coverage (11/18) adequately explained?

PROVIDE:
- **Strengths**: What works well (2-3 points)
- **Weaknesses**: What needs improvement (2-3 points with specific module/section references)
- **Critical Issues**: Any overclaims, gaps, or inconsistencies
- **Recommendations**: Concrete suggestions for axiom reduction or roadmap refinement
- **Overall Assessment**: Accept / Minor Revision / Major Revision / Reject

Focus on formal verification standards, honest assessment of proof completion, and strategic planning for full formalization.
"""

    result3 = await bridge.consult_all_experts(lean_prompt, QueryType.PEER_REVIEW)
    bridge.print_results_with_scores(result3)

    best3 = result3.get('best_response')
    quality3 = best3['quality'] if best3 else 0.0

    # Save consultation 3 result
    output_path3 = base_path / f"multi_LLM/consultation/sprint9_lean_status_{timestamp}.txt"
    with open(output_path3, 'w', encoding='utf-8') as f:
        f.write(f"Sprint 9 Phase 4 - Lean Status Report Review\n")
        f.write(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Quality Score: {quality3:.3f}\n")
        f.write("=" * 80 + "\n\n")
        for resp in result3['responses']:
            if resp.get('success'):
                f.write(f"SOURCE: {resp['source'].upper()}\n")
                f.write(f"Quality: {resp.get('quality_score', 0):.3f}\n")
                f.write("-" * 80 + "\n")
                f.write(resp['content'])
                f.write("\n\n" + "=" * 80 + "\n\n")

    print(f"\nSaved consultation 3 to: {output_path3}")

    # Final Summary
    print("\n\n" + "=" * 80)
    print("SPRINT 9 PHASE 4: CONSULTATION SUMMARY")
    print("=" * 80)

    avg_quality = (quality1 + quality2 + quality3) / 3

    print(f"\nQuality Scores:")
    print(f"  Consultation 1 (Mission Statement): {quality1:.3f}")
    print(f"  Consultation 2 (Research Roadmap):  {quality2:.3f}")
    print(f"  Consultation 3 (Lean Status Report): {quality3:.3f}")
    print(f"  Average Quality Score:               {avg_quality:.3f}")
    print(f"  Target Quality Score:                 0.700")

    if avg_quality >= 0.70:
        print(f"\n✅ PASSED: Average quality {avg_quality:.3f} meets target >0.70")
    else:
        print(f"\n⚠️ BELOW TARGET: Average quality {avg_quality:.3f} is below 0.70 target")

    # Save summary JSON
    summary = {
        'date': datetime.now().isoformat(),
        'sprint': 'Sprint 9 Phase 4',
        'deliverables': [
            'MISSION_STATEMENT.md',
            'RESEARCH_ROADMAP.md',
            'LEAN_STATUS_REPORT.md'
        ],
        'consultations': {
            'mission_statement': {
                'quality_score': quality1,
                'best_source': best1['source'] if best1 else None,
                'output_file': str(output_path1.name)
            },
            'research_roadmap': {
                'quality_score': quality2,
                'best_source': best2['source'] if best2 else None,
                'output_file': str(output_path2.name)
            },
            'lean_status': {
                'quality_score': quality3,
                'best_source': best3['source'] if best3 else None,
                'output_file': str(output_path3.name)
            }
        },
        'average_quality': avg_quality,
        'target_quality': 0.70,
        'passed': avg_quality >= 0.70
    }

    summary_path = base_path / f"multi_LLM/consultation/sprint9_summary_{timestamp}.json"
    with open(summary_path, 'w', encoding='utf-8') as f:
        json.dump(summary, f, indent=2)

    print(f"\nSaved summary to: {summary_path}")

    # Cache stats
    print("\n" + "=" * 80)
    stats = bridge.get_cache_stats()
    print(f"Cache Statistics:")
    print(f"  Total entries: {stats['total_entries']}")
    print(f"  Cache hits: {stats['cache_hits']}")
    print(f"  Cache misses: {stats['cache_misses']}")
    print(f"  Hit rate: {stats['hit_rate']:.1%}")
    print("=" * 80)

    return {
        'success': True,
        'average_quality': avg_quality,
        'summary_path': str(summary_path),
        'consultation_files': [
            str(output_path1.name),
            str(output_path2.name),
            str(output_path3.name)
        ]
    }


if __name__ == "__main__":
    result = asyncio.run(main())
    sys.exit(0 if result['success'] else 1)
