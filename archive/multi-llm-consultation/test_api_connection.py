#!/usr/bin/env python3
"""
Simple API Connection Test
Test each API with a very short query to diagnose connection issues.
"""

import asyncio
import json
from pathlib import Path
from claude_llm_bridge import MultiLLMBridge

async def test_apis():
    """Test each API with a simple query."""

    print("=" * 70)
    print("API CONNECTION TEST")
    print("=" * 70)
    print()

    bridge = MultiLLMBridge(config_path="./api_config.json")

    # Very short test query
    test_query = "What is 2+2? Respond with just the number."

    print(f"Testing with simple query: '{test_query}'")
    print()

    # Test Grok
    print("Testing Grok...")
    try:
        result = await bridge.query_grok(test_query)
        print(f"  Status: {'SUCCESS' if result['success'] else 'FAILED'}")
        if result['success']:
            print(f"  Response: {result['content'][:100]}")
        else:
            print(f"  Error: {result['error']}")
    except Exception as e:
        print(f"  Exception: {e}")

    print()

    # Test ChatGPT
    print("Testing ChatGPT...")
    try:
        result = await bridge.query_chatgpt(test_query)
        print(f"  Status: {'SUCCESS' if result['success'] else 'FAILED'}")
        if result['success']:
            print(f"  Response: {result['content'][:100]}")
        else:
            print(f"  Error: {result['error']}")
    except Exception as e:
        print(f"  Exception: {e}")

    print()

    # Test Gemini
    print("Testing Gemini...")
    try:
        result = await bridge.query_gemini(test_query)
        print(f"  Status: {'SUCCESS' if result['success'] else 'FAILED'}")
        if result['success']:
            print(f"  Response: {result['content'][:100]}")
        else:
            print(f"  Error: {result['error']}")
    except Exception as e:
        print(f"  Exception: {e}")

    print()
    print("=" * 70)
    print("Test complete")
    print("=" * 70)

if __name__ == "__main__":
    asyncio.run(test_apis())
