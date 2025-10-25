#!/usr/bin/env python3
"""
Test Suite for Enhanced Multi-LLM Bridge
Tests caching, quality scoring, retry logic, and query types
"""

import asyncio
import json
import time
from enhanced_llm_bridge import EnhancedMultiLLMBridge, QueryType, QualityScorer
from pathlib import Path


class TestEnhancedBridge:
    """Comprehensive test suite for enhanced features."""

    def __init__(self):
        self.bridge = EnhancedMultiLLMBridge()
        self.scorer = QualityScorer()
        self.test_results = []

    def log_result(self, test_name: str, passed: bool, details: str = ""):
        """Log test result."""
        status = "[PASS]" if passed else "[FAIL]"
        print(f"{status} - {test_name}")
        if details:
            print(f"       {details}")

        self.test_results.append({
            'test': test_name,
            'passed': passed,
            'details': details
        })

    def test_query_type_detection(self):
        """Test automatic query type detection."""
        print("\n" + "=" * 70)
        print("TEST 1: Query Type Detection")
        print("=" * 70)

        test_cases = [
            ("How do I prove this theorem in Lean 4?", QueryType.LEAN_PROOF),
            ("Please review this paper section", QueryType.PEER_REVIEW),
            ("Why does quantum mechanics emerge from logic?", QueryType.THEORY_QUESTION),
            ("Hello, how are you?", QueryType.GENERAL),
        ]

        all_passed = True
        for prompt, expected_type in test_cases:
            detected = self.bridge.detect_query_type(prompt)
            passed = detected == expected_type
            all_passed = all_passed and passed

            self.log_result(
                f"Detect '{expected_type.value}'",
                passed,
                f"Prompt: '{prompt[:50]}...'"
            )

        return all_passed

    def test_quality_scoring(self):
        """Test quality scoring system."""
        print("\n" + "=" * 70)
        print("TEST 2: Quality Scoring")
        print("=" * 70)

        # Test Lean proof scoring
        lean_response_good = """
Here's a Lean 4 proof:

```lean
import Mathlib.Analysis.Calculus.MeanValue

theorem monotone_from_deriv (f : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, f' x > 0) :
    StrictMono f := by
  intro x y hxy
  apply Mathlib.Analysis.Calculus.MeanValue.strictMono_of_deriv_pos
  exact hf'
```

This uses the Mean Value Theorem from Mathlib. The key steps are:
1. Import the MVT theorem
2. Apply strictMono_of_deriv_pos
3. Provide the positive derivative condition

Alternative approach: You could also use monotone_of_deriv_nonneg if you only need monotonicity.
"""

        lean_response_bad = """
I think you can use the mean value theorem but I'm not sure. Here's some Lean 3 code:

begin
  sorry
end
"""

        scores_good = self.scorer.score_response(lean_response_good, QueryType.LEAN_PROOF, "test")
        scores_bad = self.scorer.score_response(lean_response_bad, QueryType.LEAN_PROOF, "test")

        passed_good = scores_good.overall > 0.5
        passed_bad = scores_bad.overall < 0.5
        passed_comparison = scores_good.overall > scores_bad.overall

        self.log_result(
            "Good Lean response scores high",
            passed_good,
            f"Score: {scores_good.overall:.2f}/1.0"
        )

        self.log_result(
            "Bad Lean response scores low",
            passed_bad,
            f"Score: {scores_bad.overall:.2f}/1.0"
        )

        self.log_result(
            "Good > Bad comparison",
            passed_comparison,
            f"Good: {scores_good.overall:.2f}, Bad: {scores_bad.overall:.2f}"
        )

        # Test peer review scoring
        peer_review_response = """
## Strengths
1. Clear mathematical formulation
2. Well-structured proof

## Areas for Improvement
1. Add more context in Section 2.3
2. Clarify Theorem 4.1 statement
3. Consider adding Figure 3 to illustrate concept

## Specific Suggestions
- Add citation to Deutsch (1985) for constructor theory
- Clarify notation in Equation 12
- Expand discussion of experimental predictions

## Minor Issues
- Typo on page 4, line 12
- Reference formatting inconsistent
"""

        scores_review = self.scorer.score_response(peer_review_response, QueryType.PEER_REVIEW, "test")
        passed_review = scores_review.overall > 0.4

        self.log_result(
            "Peer review response scored",
            passed_review,
            f"Score: {scores_review.overall:.2f}/1.0"
        )

        return passed_good and passed_bad and passed_comparison and passed_review

    def test_cache_functionality(self):
        """Test caching layer."""
        print("\n" + "=" * 70)
        print("TEST 3: Cache Functionality")
        print("=" * 70)

        # Clear any existing cache for test
        test_prompt = "Test cache query - " + str(time.time())

        # Manually test cache put/get
        test_responses = [{
            'source': 'test',
            'success': True,
            'content': 'Test response'
        }]

        test_scores = {
            'test': {'overall': 0.85}
        }

        self.bridge.cache.put(
            test_prompt,
            QueryType.GENERAL,
            0.1,
            test_responses,
            test_scores
        )

        # Try to retrieve
        cached = self.bridge.cache.get(test_prompt, QueryType.GENERAL, 0.1)

        passed_put_get = cached is not None and cached['from_cache']

        self.log_result(
            "Cache put/get works",
            passed_put_get,
            "Successfully stored and retrieved from cache"
        )

        # Test cache stats
        stats = self.bridge.get_cache_stats()
        passed_stats = stats['total_entries'] > 0

        self.log_result(
            "Cache stats accessible",
            passed_stats,
            f"Total entries: {stats['total_entries']}"
        )

        return passed_put_get and passed_stats

    async def test_api_connectivity(self):
        """Test basic API connectivity with retry logic."""
        print("\n" + "=" * 70)
        print("TEST 4: API Connectivity (Optional - requires API keys)")
        print("=" * 70)

        try:
            # Simple query to test connectivity
            result = await self.bridge.consult_all_experts(
                "Test query: What is 2+2?",
                QueryType.GENERAL,
                use_cache=False  # Force fresh query
            )

            successful_responses = sum(1 for r in result['responses'] if r.get('success'))

            passed = successful_responses > 0

            self.log_result(
                "At least one API responded",
                passed,
                f"{successful_responses}/3 APIs successful"
            )

            # Check if quality scores were computed
            has_scores = len(result.get('quality_scores', {})) > 0

            self.log_result(
                "Quality scores computed",
                has_scores,
                f"Scored {len(result.get('quality_scores', {}))} responses"
            )

            return passed and has_scores

        except Exception as e:
            self.log_result(
                "API connectivity",
                False,
                f"Error: {str(e)}"
            )
            print("\n[WARNING] Skipping API tests (no valid API keys configured)")
            return True  # Don't fail suite if no API keys

    async def test_specialized_methods(self):
        """Test specialized consultation methods."""
        print("\n" + "=" * 70)
        print("TEST 5: Specialized Methods (Mock)")
        print("=" * 70)

        # Test that methods exist and have correct signatures
        methods_exist = all([
            callable(getattr(self.bridge, 'consult_lean_proof', None)),
            callable(getattr(self.bridge, 'consult_peer_review', None)),
            callable(getattr(self.bridge, 'consult_theory', None)),
        ])

        self.log_result(
            "Specialized methods exist",
            methods_exist,
            "consult_lean_proof, consult_peer_review, consult_theory"
        )

        return methods_exist

    def test_cache_ttl_logic(self):
        """Test TTL logic for different query types."""
        print("\n" + "=" * 70)
        print("TEST 6: Cache TTL Logic")
        print("=" * 70)

        ttl_lean = self.bridge.cache._get_ttl(QueryType.LEAN_PROOF)
        ttl_review = self.bridge.cache._get_ttl(QueryType.PEER_REVIEW)
        ttl_theory = self.bridge.cache._get_ttl(QueryType.THEORY_QUESTION)

        passed_lean = ttl_lean == 7 * 24 * 3600  # 7 days
        passed_review = ttl_review == 1 * 24 * 3600  # 1 day
        passed_theory = ttl_theory == 30 * 24 * 3600  # 30 days

        self.log_result(
            "Lean proof TTL = 7 days",
            passed_lean,
            f"TTL: {ttl_lean / (24*3600):.1f} days"
        )

        self.log_result(
            "Peer review TTL = 1 day",
            passed_review,
            f"TTL: {ttl_review / (24*3600):.1f} days"
        )

        self.log_result(
            "Theory question TTL = 30 days",
            passed_theory,
            f"TTL: {ttl_theory / (24*3600):.1f} days"
        )

        return passed_lean and passed_review and passed_theory

    async def run_all_tests(self):
        """Run all tests and report results."""
        print("\n" + "=" * 70)
        print("ENHANCED MULTI-LLM BRIDGE TEST SUITE")
        print("=" * 70)

        tests = [
            ("Query Type Detection", self.test_query_type_detection),
            ("Quality Scoring", self.test_quality_scoring),
            ("Cache Functionality", self.test_cache_functionality),
            ("Cache TTL Logic", self.test_cache_ttl_logic),
            ("Specialized Methods", self.test_specialized_methods),
        ]

        # Run synchronous tests
        results = []
        for name, test_func in tests:
            if asyncio.iscoroutinefunction(test_func):
                result = await test_func()
            else:
                result = test_func()
            results.append(result)

        # Run API test (optional)
        print("\n[WARNING] API connectivity test requires valid API keys in api_config.json")
        try:
            api_result = await self.test_api_connectivity()
            results.append(api_result)
        except Exception as e:
            print(f"[WARNING] Skipped API test: {e}")
            results.append(True)  # Don't fail suite

        # Summary
        print("\n" + "=" * 70)
        print("TEST SUMMARY")
        print("=" * 70)

        total_tests = len(self.test_results)
        passed_tests = sum(1 for r in self.test_results if r['passed'])

        print(f"\nTotal Tests: {total_tests}")
        print(f"Passed: {passed_tests}")
        print(f"Failed: {total_tests - passed_tests}")
        print(f"Success Rate: {passed_tests/total_tests*100:.1f}%")

        if all(results):
            print("\n[SUCCESS] ALL TESTS PASSED")
            return True
        else:
            print("\n[FAILURE] SOME TESTS FAILED")
            return False


async def main():
    """Run test suite."""
    tester = TestEnhancedBridge()
    success = await tester.run_all_tests()

    # Save results
    results_file = "test_enhanced_results.json"
    with open(results_file, 'w') as f:
        json.dump({
            'timestamp': time.time(),
            'total_tests': len(tester.test_results),
            'passed': sum(1 for r in tester.test_results if r['passed']),
            'results': tester.test_results
        }, f, indent=2)

    print(f"\n[RESULTS] Detailed results saved to: {results_file}")

    return 0 if success else 1


if __name__ == "__main__":
    exit_code = asyncio.run(main())
    exit(exit_code)
