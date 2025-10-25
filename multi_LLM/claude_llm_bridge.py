#!/usr/bin/env python3
"""
Multi-LLM API Bridge for Expert Consultation
Designed for Lean 4 theorem proving and formal verification tasks.
"""

import json
import requests
import asyncio
import aiohttp
import time
from typing import Dict, List, Any, Optional, Tuple
import sys
import os

class MultiLLMBridge:
    def __init__(self, config_path: str = "./api_config.json"):
        """Initialize the bridge with API configuration."""
        self.config_path = config_path
        self.config = self._load_config()
        self.session_logs = []
        
    def _load_config(self) -> Dict[str, Any]:
        """Load API configuration from JSON file."""
        try:
            with open(self.config_path, 'r') as f:
                return json.load(f)
        except FileNotFoundError:
            print(f"Error: Configuration file {self.config_path} not found.")
            print("Please ensure api_config.json exists with your API keys.")
            sys.exit(1)
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON in configuration file: {e}")
            sys.exit(1)

    async def query_grok(self, prompt: str) -> Dict[str, Any]:
        """Query Grok API asynchronously."""
        headers = {
            "Authorization": f"Bearer {self.config['api_keys']['grok']}",
            "Content-Type": "application/json"
        }
        
        payload = {
            "messages": [
                {"role": "system", "content": self.config['lean_specific_prompts']['system_prompt']},
                {"role": "user", "content": prompt}
            ],
            "model": "grok-3",
            "temperature": self.config['default_settings']['temperature'],
            "max_tokens": self.config['default_settings']['max_tokens']
        }
        
        try:
            async with aiohttp.ClientSession() as session:
                async with session.post(
                    self.config['endpoints']['grok'], 
                    headers=headers, 
                    json=payload,
                    timeout=aiohttp.ClientTimeout(total=self.config['default_settings']['timeout_seconds'])
                ) as response:
                    if response.status == 200:
                        result = await response.json()
                        return {
                            "source": "grok",
                            "success": True,
                            "content": result['choices'][0]['message']['content'],
                            "model": "grok-3"
                        }
                    else:
                        return {
                            "source": "grok",
                            "success": False,
                            "error": f"HTTP {response.status}: {await response.text()}"
                        }
        except Exception as e:
            return {
                "source": "grok",
                "success": False,
                "error": str(e)
            }

    async def query_chatgpt(self, prompt: str) -> Dict[str, Any]:
        """Query ChatGPT API asynchronously."""
        headers = {
            "Authorization": f"Bearer {self.config['api_keys']['chatgpt']}",
            "Content-Type": "application/json"
        }
        
        payload = {
            "model": "gpt-4",
            "messages": [
                {"role": "system", "content": self.config['lean_specific_prompts']['system_prompt']},
                {"role": "user", "content": prompt}
            ],
            "temperature": self.config['default_settings']['temperature'],
            "max_tokens": self.config['default_settings']['max_tokens']
        }
        
        try:
            async with aiohttp.ClientSession() as session:
                async with session.post(
                    self.config['endpoints']['chatgpt'], 
                    headers=headers, 
                    json=payload,
                    timeout=aiohttp.ClientTimeout(total=self.config['default_settings']['timeout_seconds'])
                ) as response:
                    if response.status == 200:
                        result = await response.json()
                        return {
                            "source": "chatgpt",
                            "success": True,
                            "content": result['choices'][0]['message']['content'],
                            "model": "gpt-4"
                        }
                    else:
                        return {
                            "source": "chatgpt",
                            "success": False,
                            "error": f"HTTP {response.status}: {await response.text()}"
                        }
        except Exception as e:
            return {
                "source": "chatgpt",
                "success": False,
                "error": str(e)
            }

    async def query_gemini(self, prompt: str) -> Dict[str, Any]:
        """Query Gemini API asynchronously."""
        url = f"{self.config['endpoints']['gemini']}?key={self.config['api_keys']['gemini']}"
        
        payload = {
            "contents": [
                {
                    "parts": [
                        {"text": f"{self.config['lean_specific_prompts']['system_prompt']}\n\n{prompt}"}
                    ]
                }
            ],
            "generationConfig": {
                "temperature": self.config['default_settings']['temperature'],
                "maxOutputTokens": self.config['default_settings']['max_tokens']
            }
        }
        
        try:
            async with aiohttp.ClientSession() as session:
                async with session.post(
                    url, 
                    json=payload,
                    timeout=aiohttp.ClientTimeout(total=self.config['default_settings']['timeout_seconds'])
                ) as response:
                    if response.status == 200:
                        result = await response.json()
                        content = result['candidates'][0]['content']['parts'][0]['text']
                        return {
                            "source": "gemini",
                            "success": True,
                            "content": content,
                            "model": "gemini-pro"
                        }
                    else:
                        return {
                            "source": "gemini",
                            "success": False,
                            "error": f"HTTP {response.status}: {await response.text()}"
                        }
        except Exception as e:
            return {
                "source": "gemini",
                "success": False,
                "error": str(e)
            }

    async def consult_all_experts(self, prompt: str) -> List[Dict[str, Any]]:
        """Query all LLM experts concurrently."""
        tasks = [
            self.query_grok(prompt),
            self.query_chatgpt(prompt),
            self.query_gemini(prompt)
        ]
        
        print("Consulting expert LLMs...")
        results = await asyncio.gather(*tasks, return_exceptions=True)
        
        # Handle exceptions and format results
        formatted_results = []
        for i, result in enumerate(results):
            if isinstance(result, Exception):
                formatted_results.append({
                    "source": ["grok", "chatgpt", "gemini"][i],
                    "success": False,
                    "error": str(result)
                })
            else:
                formatted_results.append(result)
        
        return formatted_results

    def validate_lean4_response(self, response_text: str) -> Dict[str, Any]:
        """Validate if response is Lean 4 (not Lean 3) and flag issues."""
        lean3_indicators = [
            'import analysis.',
            'import data.',
            'import tactic.',
            'begin\n',
            'begin ',
            ', begin',
            '\nend\n',
            ' end\n',
            'cases\'',
            'have ... :=',
        ]

        lean4_indicators = [
            'import Mathlib.',
            'by\n',
            'by ',
            ', by',
            'obtain',
            'rcases',
        ]

        lean3_count = sum(1 for indicator in lean3_indicators if indicator in response_text)
        lean4_count = sum(1 for indicator in lean4_indicators if indicator in response_text)

        is_lean3 = lean3_count > 0 and lean3_count > lean4_count
        is_lean4 = lean4_count > 0 and lean4_count > lean3_count

        return {
            'is_lean3': is_lean3,
            'is_lean4': is_lean4,
            'lean3_count': lean3_count,
            'lean4_count': lean4_count,
            'warning': 'Response contains Lean 3 syntax!' if is_lean3 else None
        }

    def synthesize_responses(self, responses: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Synthesize expert responses into actionable recommendations."""
        successful_responses = [r for r in responses if r.get('success', False)]
        failed_responses = [r for r in responses if not r.get('success', False)]

        if not successful_responses:
            return {
                "synthesis_success": False,
                "error": "All expert consultations failed",
                "failed_responses": failed_responses
            }

        # Validate Lean 4 vs Lean 3 for each response
        lean_validations = {}
        for response in successful_responses:
            validation = self.validate_lean4_response(response.get('content', ''))
            if validation['warning']:
                lean_validations[response['source']] = validation
        
        # Extract key insights from successful responses
        recommendations = {
            "mvt_approaches": [],
            "mathlib_theorems": [],
            "alternative_strategies": [],
            "lean_code_suggestions": []
        }
        
        # Simple keyword-based extraction (could be enhanced with NLP)
        for response in successful_responses:
            content = response.get('content', '').lower()
            
            # Look for MVT-related suggestions
            if any(keyword in content for keyword in ['mean value', 'mvt', 'rolle', 'derivative']):
                recommendations["mvt_approaches"].append({
                    "source": response['source'],
                    "suggestion": response['content']
                })
            
            # Look for Mathlib theorem mentions
            if any(keyword in content for keyword in ['mathlib', 'real.', 'continuous', 'differentiable']):
                recommendations["mathlib_theorems"].append({
                    "source": response['source'],
                    "suggestion": response['content']
                })
            
            # Look for alternative strategies
            if any(keyword in content for keyword in ['alternative', 'instead', 'monotonic', 'strict']):
                recommendations["alternative_strategies"].append({
                    "source": response['source'],
                    "suggestion": response['content']
                })
            
            # Look for Lean code
            if '```lean' in response['content'] or 'theorem ' in content or 'have ' in content:
                recommendations["lean_code_suggestions"].append({
                    "source": response['source'],
                    "suggestion": response['content']
                })
        
        return {
            "synthesis_success": True,
            "total_experts": len(responses),
            "successful_consultations": len(successful_responses),
            "failed_consultations": len(failed_responses),
            "lean_validations": lean_validations,
            "recommendations": recommendations,
            "raw_responses": successful_responses
        }

    def format_lean_consultation_prompt(self, 
                                       theorem_name: str,
                                       current_code: str,
                                       specific_issue: str,
                                       context: str = "") -> str:
        """Format a comprehensive prompt for Lean 4 consultation."""
        return f"""
LEAN 4 THEOREM PROVING CONSULTATION

THEOREM: {theorem_name}

CURRENT ISSUE: {specific_issue}

CURRENT CODE:
```lean
{current_code}
```

CONTEXT: {context}

SPECIFIC REQUESTS:
1. Best approach to prove monotonicity from positive derivative in Lean 4
2. What Mathlib theorems exist for Mean Value Theorem that I should use
3. Alternative proof strategies that avoid MVT complexity
4. Working Lean 4 code suggestions for immediate implementation

Please provide:
- Concrete Mathlib theorem names and imports
- Working Lean 4 code snippets
- Step-by-step proof strategies
- Alternative approaches if MVT is too complex

Focus on actionable, implementable solutions with proper Lean 4 syntax.
"""

    async def lean_mvt_consultation(self, 
                                  theorem_code: str, 
                                  issue_description: str,
                                  context: str = "") -> Dict[str, Any]:
        """Specialized consultation for Lean 4 MVT problems."""
        
        prompt = self.format_lean_consultation_prompt(
            theorem_name="temporal_ordering monotonicity",
            current_code=theorem_code,
            specific_issue=issue_description,
            context=context
        )
        
        print("Consulting experts on Lean 4 MVT formalization...")
        print("Issue:", issue_description.encode('utf-8', errors='replace').decode('utf-8'))
        print("-" * 50)
        
        responses = await self.consult_all_experts(prompt)
        synthesis = self.synthesize_responses(responses)
        
        return {
            "consultation_type": "lean_mvt",
            "timestamp": time.time(),
            "prompt": prompt,
            "responses": responses,
            "synthesis": synthesis
        }

    def save_consultation_log(self, consultation_result: Dict[str, Any], 
                            filename: Optional[str] = None) -> str:
        """Save consultation results to a log file."""
        if filename is None:
            timestamp = int(time.time())
            filename = f"consultation_log_{timestamp}.json"
        
        filepath = os.path.join(os.path.dirname(self.config_path), filename)
        
        with open(filepath, 'w') as f:
            json.dump(consultation_result, f, indent=2, default=str)
        
        return filepath

    def print_synthesis_summary(self, synthesis: Dict[str, Any]):
        """Print a formatted summary of the expert consultation synthesis."""
        if not synthesis.get('synthesis_success', False):
            print("[ERROR] Expert consultation failed:")
            print(synthesis.get('error', 'Unknown error'))
            return

        print(f"[SUCCESS] Expert Consultation Summary")
        print(f"Successfully consulted {synthesis['successful_consultations']}/{synthesis['total_experts']} experts")

        if synthesis['failed_consultations'] > 0:
            print(f"[WARNING] {synthesis['failed_consultations']} consultation(s) failed")

        # Show Lean 3 vs Lean 4 validation warnings
        lean_validations = synthesis.get('lean_validations', {})
        if lean_validations:
            print("\n[WARNING] Lean Version Issues Detected:")
            for source, validation in lean_validations.items():
                print(f"  {source.upper()}: {validation['warning']}")
                print(f"    Lean 3 indicators: {validation['lean3_count']}, Lean 4 indicators: {validation['lean4_count']}")

        print("\n" + "="*60)
        
        recommendations = synthesis.get('recommendations', {})
        
        if recommendations.get('mvt_approaches'):
            print("\n[MVT] MEAN VALUE THEOREM APPROACHES:")
            for i, approach in enumerate(recommendations['mvt_approaches'], 1):
                print(f"{i}. From {approach['source'].upper()}:")
                print(f"   {approach['suggestion'][:200]}...")
        
        if recommendations.get('mathlib_theorems'):
            print("\n[MATHLIB] THEOREMS IDENTIFIED:")
            for i, theorem in enumerate(recommendations['mathlib_theorems'], 1):
                print(f"{i}. From {theorem['source'].upper()}:")
                print(f"   {theorem['suggestion'][:200]}...")
        
        if recommendations.get('alternative_strategies'):
            print("\n[ALT] ALTERNATIVE STRATEGIES:")
            for i, strategy in enumerate(recommendations['alternative_strategies'], 1):
                print(f"{i}. From {strategy['source'].upper()}:")
                print(f"   {strategy['suggestion'][:200]}...")
        
        if recommendations.get('lean_code_suggestions'):
            print("\n[CODE] LEAN CODE SUGGESTIONS:")
            for i, code in enumerate(recommendations['lean_code_suggestions'], 1):
                print(f"{i}. From {code['source'].upper()}:")
                print(f"   {code['suggestion'][:300]}...")

async def main():
    """Main function for command-line usage."""
    if len(sys.argv) < 2:
        print("Usage: python claude_llm_bridge.py <issue_description>")
        print("Or import as module for programmatic use")
        return
    
    issue_description = " ".join(sys.argv[1:])
    
    # Example Lean code for the MVT issue
    example_theorem_code = """
theorem temporal_ordering (ε₁ ε₂ : ℝ) (h₁ : ε₁ > 0) (h₂ : ε₂ > 0) :
  ε₁ < ε₂ ↔ C ε₁ < C ε₂ := by
  -- Need to prove C(ε) is strictly monotonic from positive derivative
  -- ConstraintRate ε > 0 for ε > 0 (already proven)
  -- But how to use MVT properly in Lean 4?
  sorry
"""
    
    bridge = MultiLLMBridge()
    
    result = await bridge.lean_mvt_consultation(
        theorem_code=example_theorem_code,
        issue_description=issue_description,
        context="Logic Field Theory formal verification - proving temporal ordering from constraint accumulation monotonicity"
    )
    
    # Print synthesis summary
    bridge.print_synthesis_summary(result['synthesis'])
    
    # Save detailed log
    log_file = bridge.save_consultation_log(result)
    print(f"\n[LOG] Detailed consultation log saved to: {log_file}")

if __name__ == "__main__":
    asyncio.run(main())