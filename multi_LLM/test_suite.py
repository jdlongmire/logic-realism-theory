#!/usr/bin/env python3
"""
Multi-LLM API Test Suite
Tests all configured LLM APIs for connectivity and proper response format.
"""

import asyncio
import json
import sys
from claude_llm_bridge import MultiLLMBridge

class MultiLLMTester:
    def __init__(self):
        self.bridge = MultiLLMBridge()
        self.results = {}

    def print_header(self, text):
        """Print formatted header"""
        print("\n" + "="*60)
        print(f"  {text}")
        print("="*60)

    def print_test(self, api_name, status, message=""):
        """Print test result"""
        symbol = "[OK]" if status else "[FAIL]"
        status_text = "PASS" if status else "FAIL"
        print(f"{symbol} {api_name:15} {status_text:6}  {message}")

    async def test_configuration(self):
        """Test configuration loading"""
        self.print_header("Configuration Test")

        try:
            config = self.bridge.config

            # Check API keys exist
            has_grok = bool(config['api_keys'].get('grok'))
            has_chatgpt = bool(config['api_keys'].get('chatgpt'))
            has_gemini = bool(config['api_keys'].get('gemini'))

            self.print_test("Grok API Key", has_grok)
            self.print_test("ChatGPT API Key", has_chatgpt)
            self.print_test("Gemini API Key", has_gemini)

            # Check endpoints
            grok_endpoint = config['endpoints']['grok']
            chatgpt_endpoint = config['endpoints']['chatgpt']
            gemini_endpoint = config['endpoints']['gemini']

            print(f"\nEndpoints:")
            print(f"  Grok:    {grok_endpoint}")
            print(f"  ChatGPT: {chatgpt_endpoint}")
            print(f"  Gemini:  {gemini_endpoint}")

            # Check if Gemini uses correct model
            gemini_correct = "gemini-1.5-flash" in gemini_endpoint or "gemini-1.5-pro" in gemini_endpoint
            self.print_test("Gemini Endpoint", gemini_correct,
                          "Uses gemini-1.5-* model" if gemini_correct else "WARNING: May use deprecated model")

            return has_grok and has_chatgpt and has_gemini

        except Exception as e:
            print(f"Configuration Error: {e}")
            return False

    async def test_individual_api(self, api_name, query_func):
        """Test individual API"""
        test_prompt = "What is Lean 4? Respond in one sentence."

        try:
            result = await query_func(test_prompt)

            if result['success']:
                content_preview = result['content'][:100] + "..." if len(result['content']) > 100 else result['content']
                self.print_test(api_name, True, f"Response: {content_preview}")

                # Check for Lean 3 vs Lean 4 in response
                content_lower = result['content'].lower()
                if 'lean 3' in content_lower and 'lean 4' not in content_lower:
                    print(f"  ⚠️  WARNING: Response may be Lean 3 focused")

                self.results[api_name] = {
                    'status': 'success',
                    'response_length': len(result['content']),
                    'model': result.get('model', 'unknown')
                }
                return True
            else:
                error_msg = result.get('error', 'Unknown error')
                self.print_test(api_name, False, f"Error: {error_msg[:80]}")
                self.results[api_name] = {
                    'status': 'failed',
                    'error': error_msg
                }
                return False

        except Exception as e:
            self.print_test(api_name, False, f"Exception: {str(e)[:80]}")
            self.results[api_name] = {
                'status': 'exception',
                'error': str(e)
            }
            return False

    async def test_apis(self):
        """Test all APIs individually"""
        self.print_header("Individual API Tests")

        grok_result = await self.test_individual_api("Grok", self.bridge.query_grok)
        chatgpt_result = await self.test_individual_api("ChatGPT", self.bridge.query_chatgpt)
        gemini_result = await self.test_individual_api("Gemini", self.bridge.query_gemini)

        return grok_result, chatgpt_result, gemini_result

    async def test_parallel_consultation(self):
        """Test parallel consultation feature"""
        self.print_header("Parallel Consultation Test")

        test_prompt = "Explain the Mean Value Theorem in one sentence."

        try:
            results = await self.bridge.consult_all_experts(test_prompt)

            successful = [r for r in results if r.get('success', False)]
            failed = [r for r in results if not r.get('success', False)]

            print(f"Parallel consultation completed:")
            print(f"  Successful: {len(successful)}/3")
            print(f"  Failed: {len(failed)}/3")

            for result in results:
                status = result.get('success', False)
                source = result['source']
                self.print_test(source, status,
                              f"Responded in parallel" if status else f"Failed: {result.get('error', 'Unknown')[:40]}")

            return len(successful) >= 1  # At least one should work

        except Exception as e:
            print(f"Parallel consultation error: {e}")
            return False

    async def test_synthesis(self):
        """Test response synthesis"""
        self.print_header("Response Synthesis Test")

        test_prompt = "How do I prove monotonicity from positive derivative in Lean 4?"

        try:
            results = await self.bridge.consult_all_experts(test_prompt)
            synthesis = self.bridge.synthesize_responses(results)

            if synthesis['synthesis_success']:
                print(f"Synthesis successful:")
                print(f"  Total experts: {synthesis['total_experts']}")
                print(f"  Successful: {synthesis['successful_consultations']}")
                print(f"  Failed: {synthesis['failed_consultations']}")

                recs = synthesis['recommendations']
                print(f"\nRecommendations extracted:")
                print(f"  MVT approaches: {len(recs.get('mvt_approaches', []))}")
                print(f"  Mathlib theorems: {len(recs.get('mathlib_theorems', []))}")
                print(f"  Alternative strategies: {len(recs.get('alternative_strategies', []))}")
                print(f"  Lean code: {len(recs.get('lean_code_suggestions', []))}")

                has_recommendations = any(len(v) > 0 for v in recs.values())
                self.print_test("Synthesis", has_recommendations,
                              "Extracted recommendations" if has_recommendations else "No recommendations found")
                return has_recommendations
            else:
                print(f"Synthesis failed: {synthesis.get('error', 'Unknown')}")
                return False

        except Exception as e:
            print(f"Synthesis error: {e}")
            return False

    async def run_all_tests(self):
        """Run complete test suite"""
        print("\n" + "#"*60)
        print("#  Multi-LLM API Test Suite")
        print("#"*60)

        # Test 1: Configuration
        config_ok = await self.test_configuration()

        # Test 2: Individual APIs
        grok_ok, chatgpt_ok, gemini_ok = await self.test_apis()

        # Test 3: Parallel consultation
        parallel_ok = await self.test_parallel_consultation()

        # Test 4: Synthesis
        synthesis_ok = await self.test_synthesis()

        # Summary
        self.print_header("Test Summary")

        total_tests = 5
        passed_tests = sum([config_ok, grok_ok, chatgpt_ok, gemini_ok, parallel_ok, synthesis_ok])

        print(f"\nOverall Results: {passed_tests}/{total_tests+1} tests passed")
        print(f"\nAPI Status:")
        print(f"  Grok:    {'[OK] Working' if grok_ok else '[FAIL] Failed'}")
        print(f"  ChatGPT: {'[OK] Working' if chatgpt_ok else '[FAIL] Failed'}")
        print(f"  Gemini:  {'[OK] Working' if gemini_ok else '[FAIL] Failed'}")
        print(f"\nFeatures:")
        print(f"  Parallel Consultation: {'[OK] Working' if parallel_ok else '[FAIL] Failed'}")
        print(f"  Response Synthesis:    {'[OK] Working' if synthesis_ok else '[FAIL] Failed'}")

        # Save results
        results_file = 'test_results.json'
        with open(results_file, 'w') as f:
            json.dump({
                'timestamp': None,  # Will be set by json
                'config_ok': config_ok,
                'api_results': {
                    'grok': grok_ok,
                    'chatgpt': chatgpt_ok,
                    'gemini': gemini_ok
                },
                'parallel_ok': parallel_ok,
                'synthesis_ok': synthesis_ok,
                'detailed_results': self.results
            }, f, indent=2, default=str)

        print(f"\nDetailed results saved to: {results_file}")

        # Recommendations
        if not grok_ok or not gemini_ok:
            self.print_header("Recommendations")
            if not grok_ok:
                print("[!] Grok API failing:")
                print("   1. Verify API key is valid")
                print("   2. Check https://api.x.ai endpoint is accessible")
                print("   3. Check for rate limiting")
            if not gemini_ok:
                print("[!] Gemini API failing:")
                print("   1. Verify API key is valid")
                print("   2. Endpoint should use gemini-1.5-flash or gemini-1.5-pro")
                print("   3. Check https://generativelanguage.googleapis.com is accessible")

        return passed_tests >= 3  # At least ChatGPT + 2 features should work

async def main():
    tester = MultiLLMTester()
    success = await tester.run_all_tests()
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    asyncio.run(main())
