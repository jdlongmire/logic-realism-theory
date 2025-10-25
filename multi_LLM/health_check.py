#!/usr/bin/env python3
"""
Multi-LLM API Health Check
Quick validation that all APIs are configured and responding
"""

import asyncio
import sys
from enhanced_llm_bridge import EnhancedMultiLLMBridge


async def main():
    """Run health check on all APIs."""
    print("\nMulti-LLM API Health Check")
    print("Testing API connectivity and response times...\n")

    bridge = EnhancedMultiLLMBridge()

    # Run health check
    health = await bridge.health_check()

    # Print results
    bridge.print_health_check(health)

    # Additional diagnostics
    if health['overall_status'] == 'healthy':
        print("\n[SUCCESS] All APIs operational and ready for use")
        return 0
    elif health['overall_status'] == 'degraded':
        print("\n[WARNING] Some APIs unavailable - system will work with reduced capacity")
        failed = [name for name, status in health['api_status'].items() if not status['status']]
        print(f"Failed APIs: {', '.join(failed)}")
        print("\nTroubleshooting:")
        print("1. Check API keys in api_config.json")
        print("2. Verify network connectivity")
        print("3. Check API service status pages")
        return 1
    else:
        print("\n[ERROR] No APIs available - system cannot function")
        print("\nTroubleshooting:")
        print("1. Verify api_config.json exists and has valid keys")
        print("2. Check network/firewall settings")
        print("3. Verify API endpoints are correct")
        print("4. Run: python3 test_api_connection.py for detailed diagnostics")
        return 2


if __name__ == "__main__":
    exit_code = asyncio.run(main())
    sys.exit(exit_code)
