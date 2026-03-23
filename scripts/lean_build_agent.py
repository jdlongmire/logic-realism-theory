#!/usr/bin/env python3
"""
LRT Lean Build Agent
Extension to physics_agent.py handling lean_build and lean_proof task types.

Handles:
  - lean_build: Full lake build, axiom/sorry count, structured report committed to repo
  - lean_proof: Apply a Lean proof attempt from task details, validate, report back

Reports are committed to docs/formalization/build-reports/ in the LRT repo.
Results are posted as GitHub issue comments when an issue number is specified.
"""

import subprocess
import json
import os
import re
import time
from pathlib import Path
from datetime import datetime
from dataclasses import dataclass
from typing import Optional

# ─────────────────────────────────────────────
# Configuration (mirrors physics_agent.py paths)
# ─────────────────────────────────────────────

# Resolve repo root relative to this script (scripts/ is one level below repo root)
LRT_REPO = Path(__file__).parent.parent.resolve()
FORMALIZATION_DIR = LRT_REPO / "formalization"  # lake build runs here
BUILD_REPORTS_DIR = LRT_REPO / "docs" / "formalization" / "build-reports"
LEAN_SRC_DIR = FORMALIZATION_DIR / "LrtFormalization"

BUILD_TIMEOUT = 1200   # 20 min — Mathlib builds can be slow even with cache
PROOF_TIMEOUT = 300    # 5 min per proof attempt

ELAN_ENV = Path.home() / ".elan" / "env"


# ─────────────────────────────────────────────
# Environment setup
# ─────────────────────────────────────────────

def get_lean_env() -> dict:
    """Get environment with elan/lean binaries on PATH."""
    env = os.environ.copy()
    # Source elan env — adds ~/.elan/bin to PATH
    elan_bin = Path.home() / ".elan" / "bin"
    if elan_bin.exists():
        env["PATH"] = str(elan_bin) + ":" + env.get("PATH", "")
    return env


def lean_available() -> bool:
    """Check if lake is available."""
    env = get_lean_env()
    result = subprocess.run(["which", "lake"], capture_output=True, env=env)
    return result.returncode == 0


# ─────────────────────────────────────────────
# Build execution
# ─────────────────────────────────────────────

@dataclass
class BuildResult:
    success: bool
    duration: float
    job_count: int
    error_count: int
    warning_count: int
    sorry_count: int
    axiom_count: int
    primitive_axioms: list
    external_axioms: list
    remaining_axioms: list
    errors: list
    raw_log: str
    timestamp: str


def run_lean_build(fetch_cache: bool = True) -> BuildResult:
    """Run lake build and parse results."""
    env = get_lean_env()
    start = time.time()
    timestamp = datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ")

    # Step 1: Fetch Mathlib cache
    if fetch_cache:
        cache_result = subprocess.run(
            ["lake", "exe", "cache", "get"],
            cwd=FORMALIZATION_DIR,
            capture_output=True, text=True,
            timeout=300, env=env
        )
        cache_log = cache_result.stdout + cache_result.stderr
    else:
        cache_log = "(cache fetch skipped)\n"

    # Step 2: Run build
    build_result = subprocess.run(
        ["lake", "build"],
        cwd=FORMALIZATION_DIR,
        capture_output=True, text=True,
        timeout=BUILD_TIMEOUT, env=env
    )

    duration = time.time() - start
    raw_log = cache_log + "\n=== lake build ===\n" + build_result.stdout + build_result.stderr

    # Parse build output
    job_count = _parse_job_count(raw_log)
    error_count = _count_pattern(raw_log, r"^error:", re.MULTILINE)
    warning_count = _count_pattern(raw_log, r"^warning:", re.MULTILINE)
    errors = _extract_errors(raw_log)

    # Step 3: Count sorries and axioms in source
    sorry_count, sorry_locations = _count_sorries()
    axioms = _count_axioms()

    return BuildResult(
        success=(build_result.returncode == 0 and error_count == 0),
        duration=duration,
        job_count=job_count,
        error_count=error_count,
        warning_count=warning_count,
        sorry_count=sorry_count,
        axiom_count=len(axioms["all"]),
        primitive_axioms=axioms["primitive"],
        external_axioms=axioms["external"],
        remaining_axioms=axioms["remaining"],
        errors=errors,
        raw_log=raw_log[:8000],  # Cap log size
        timestamp=timestamp,
    )


def _parse_job_count(log: str) -> int:
    """Extract completed job count from lake build output."""
    match = re.search(r"(\d+) jobs?", log)
    return int(match.group(1)) if match else 0


def _count_pattern(text: str, pattern: str, flags=0) -> int:
    return len(re.findall(pattern, text, flags))


def _extract_errors(log: str) -> list:
    """Extract error lines from build log."""
    errors = []
    for line in log.split("\n"):
        if re.match(r"^\s*error:", line, re.IGNORECASE):
            errors.append(line.strip())
    return errors[:20]  # Cap at 20


def _count_sorries() -> tuple:
    """Count sorry occurrences in Lean source files."""
    count = 0
    locations = []
    if not LEAN_SRC_DIR.exists():
        return 0, []
    for lean_file in LEAN_SRC_DIR.rglob("*.lean"):
        for i, line in enumerate(lean_file.read_text(errors="replace").splitlines(), 1):
            # Skip comment lines
            stripped = line.strip()
            if stripped.startswith("--"):
                continue
            if "sorry" in line:
                count += 1
                rel = lean_file.relative_to(LRT_REPO)
                locations.append(f"{rel}:{i}: {stripped[:80]}")
    return count, locations


def _count_axioms() -> dict:
    """Count and classify axioms in Lean source."""
    all_axioms = []
    if not LEAN_SRC_DIR.exists():
        return {"all": [], "primitive": [], "external": [], "remaining": []}

    for lean_file in LEAN_SRC_DIR.rglob("*.lean"):
        text = lean_file.read_text(errors="replace")
        for match in re.finditer(r"^axiom\s+(\w+)", text, re.MULTILINE):
            name = match.group(1)
            all_axioms.append(name)

    # Classify based on known naming conventions
    primitive = [a for a in all_axioms if any(
        k in a.lower() for k in ["i_infinite", "i∞", "bridge_principle", "infinite_info"]
    )]
    external = [a for a in all_axioms if any(
        k in a.lower() for k in ["gleason", "stone", "hardy", "masanes", "cdp",
                                   "noether", "debreu", "nachbin", "wigner", "von_neumann"]
    )]
    remaining = [a for a in all_axioms if a not in primitive and a not in external]

    return {
        "all": all_axioms,
        "primitive": primitive,
        "external": external,
        "remaining": remaining,
    }


# ─────────────────────────────────────────────
# Report generation
# ─────────────────────────────────────────────

def generate_build_report(result: BuildResult, task_id: str) -> str:
    """Generate a structured Markdown build report."""
    status_icon = "✅ SUCCESS" if result.success else "❌ FAILED"
    sorry_icon = "✅" if result.sorry_count == 0 else "⚠️"
    axiom_total = result.axiom_count

    report = f"""# Lean Build Report — {result.timestamp}

**Task:** {task_id}  
**Status:** {status_icon}  
**Duration:** {result.duration:.1f}s  
**Jobs:** {result.job_count}  
**Errors:** {result.error_count}  
**Warnings:** {result.warning_count}  

---

## Axiom Inventory

| Category | Count |
|----------|-------|
| **Total** | {axiom_total} |
| PRIMITIVE | {len(result.primitive_axioms)} |
| EXTERNAL (Tier 2) | {len(result.external_axioms)} |
| REMAINING | {len(result.remaining_axioms)} |

"""

    if result.primitive_axioms:
        report += "**Primitive:** " + ", ".join(f"`{a}`" for a in result.primitive_axioms) + "\n\n"
    if result.remaining_axioms:
        report += "**Remaining (derivation targets):**\n"
        for a in result.remaining_axioms:
            report += f"- `{a}`\n"
        report += "\n"

    report += f"""---

## Sorry Count

{sorry_icon} **{result.sorry_count} sorries**

"""

    if result.error_count > 0:
        report += "---\n\n## Errors\n\n"
        for err in result.errors:
            report += f"```\n{err}\n```\n\n"

    report += f"""---

## Build Log (truncated)

```
{result.raw_log[-3000:]}
```

---

*Generated by ThinxS Lean Build Agent — {result.timestamp}*  
*Human-Curated, AI-Enabled (HCAE)*
"""
    return report


# ─────────────────────────────────────────────
# GitHub integration
# ─────────────────────────────────────────────

def post_github_comment(issue_number: int, body: str) -> bool:
    """Post a comment to a GitHub issue."""
    result = subprocess.run(
        ["gh", "api",
         f"repos/jdlongmire/logic-realism-theory/issues/{issue_number}/comments",
         "--method", "POST",
         "--field", f"body={body}"],
        capture_output=True, text=True, cwd=LRT_REPO
    )
    return result.returncode == 0


def commit_and_push(file_path: Path, message: str) -> bool:
    """Commit a single file and push."""
    try:
        subprocess.run(["git", "add", str(file_path)],
                       cwd=LRT_REPO, check=True, capture_output=True)
        subprocess.run(["git", "commit", "-m", message],
                       cwd=LRT_REPO, check=True, capture_output=True)
        subprocess.run(["git", "push"],
                       cwd=LRT_REPO, check=True, capture_output=True)
        return True
    except subprocess.CalledProcessError:
        return False


# ─────────────────────────────────────────────
# Task handlers (called from physics_agent.py)
# ─────────────────────────────────────────────

def handle_lean_build(task) -> tuple[bool, str]:
    """
    Handle lean_build task type.
    Runs full lake build, generates report, commits to repo.
    Returns (success, output_summary).
    """
    if not lean_available():
        return False, "lake not found — is elan installed? Check ~/.elan/bin"

    BUILD_REPORTS_DIR.mkdir(parents=True, exist_ok=True)

    # Run build
    result = run_lean_build(fetch_cache=True)

    # Generate report
    report_md = generate_build_report(result, task.task_id)

    # Write report file
    date_str = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    report_file = BUILD_REPORTS_DIR / f"build-report-{date_str}.md"
    report_file.write_text(report_md)

    # Also update the "latest" symlink-style file for easy reading
    latest_file = BUILD_REPORTS_DIR / "LATEST.md"
    latest_file.write_text(report_md)

    # Commit
    commit_msg = (
        f"build(lean): {'SUCCESS' if result.success else 'FAILED'} — "
        f"{result.job_count} jobs, {result.axiom_count} axioms, "
        f"{result.sorry_count} sorries [{task.task_id}]"
    )
    committed = commit_and_push(BUILD_REPORTS_DIR, commit_msg)

    # Post to GitHub issue if specified
    issue_num = _extract_issue_number(task.details)
    if issue_num:
        comment = f"## Lean Build Result — {task.task_id}\n\n"
        comment += f"**Status:** {'✅ SUCCESS' if result.success else '❌ FAILED'}  \n"
        comment += f"**Jobs:** {result.job_count} | **Axioms:** {result.axiom_count} | **Sorries:** {result.sorry_count}  \n"
        comment += f"**Duration:** {result.duration:.1f}s\n\n"
        if result.error_count > 0:
            comment += f"**Errors ({result.error_count}):**\n```\n"
            comment += "\n".join(result.errors[:5])
            comment += "\n```\n"
        comment += f"\nFull report: `docs/formalization/build-reports/build-report-{date_str}.md`"
        post_github_comment(issue_num, comment)

    summary = (
        f"Build {'SUCCESS' if result.success else 'FAILED'}: "
        f"{result.job_count} jobs, {result.axiom_count} axioms, "
        f"{result.sorry_count} sorries, {result.error_count} errors. "
        f"Report: {report_file.name}. Committed: {committed}"
    )
    return result.success, summary


def handle_lean_proof(task) -> tuple[bool, str]:
    """
    Handle lean_proof task type.
    Applies Lean code from task details to target file, validates, reports.
    Does NOT commit on failure — only commits if build succeeds.
    Returns (success, output_summary).
    """
    if not lean_available():
        return False, "lake not found — is elan installed?"

    # Extract proof code from task details
    proof_code = _extract_code_block(task.details)
    if not proof_code:
        return False, "No Lean code block found in task details. Expected ```lean ... ``` block."

    # Identify target file
    target_path = LRT_REPO / task.target
    if not target_path.exists():
        return False, f"Target file not found: {target_path}"

    # Back up original
    original_content = target_path.read_text()

    # Apply patch — find the axiom declaration and replace with proof
    claim_name = _extract_claim_name(task.details)
    if claim_name:
        patched = _apply_proof_patch(original_content, claim_name, proof_code)
        if patched is None:
            return False, f"Could not find axiom '{claim_name}' in {target_path.name}"
        target_path.write_text(patched)
    else:
        # Full file replacement mode
        target_path.write_text(proof_code)

    # Validate with lake build (just this file's module)
    env = get_lean_env()
    build_result = subprocess.run(
        ["lake", "build", f"LrtFormalization.{target_path.stem}"],
        cwd=FORMALIZATION_DIR,
        capture_output=True, text=True,
        timeout=PROOF_TIMEOUT, env=env
    )

    success = build_result.returncode == 0
    build_output = build_result.stdout + build_result.stderr

    if success:
        # Verify no new sorries introduced
        sorry_count, _ = _count_sorries()
        if sorry_count > 0:
            target_path.write_text(original_content)  # Rollback
            return False, f"Build succeeded but introduced {sorry_count} sorry(s). Rolled back."

        # Commit
        commit_msg = f"proof(lean): {task.task_id} — {task.description}\n\nAddresses: #{_extract_issue_number(task.details) or 'unknown'}"
        committed = commit_and_push(target_path, commit_msg)

        # Post success to GitHub
        issue_num = _extract_issue_number(task.details)
        if issue_num:
            comment = (
                f"## ✅ Lean Proof Validated — {task.task_id}\n\n"
                f"**Claim:** {task.description}\n"
                f"**File:** `{task.target}`\n\n"
                f"Build succeeded with 0 sorries. Committed and pushed.\n\n"
                f"```\n{build_output[:500]}\n```"
            )
            post_github_comment(issue_num, comment)

        return True, f"Proof validated and committed: {task.task_id}"
    else:
        # Rollback
        target_path.write_text(original_content)

        # Post failure to GitHub
        issue_num = _extract_issue_number(task.details)
        if issue_num:
            comment = (
                f"## ❌ Lean Proof Failed — {task.task_id}\n\n"
                f"**Claim:** {task.description}\n"
                f"**File:** `{task.target}`\n\n"
                f"Build failed. Original file restored. Error output:\n\n"
                f"```\n{build_output[:1500]}\n```\n\n"
                f"Perplexity Computer: please revise the proof attempt."
            )
            post_github_comment(issue_num, comment)

        return False, f"Proof failed. Rolled back. Errors: {build_output[:500]}"


# ─────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────

def _extract_issue_number(details: str) -> Optional[int]:
    """Extract GitHub issue number from task details string."""
    match = re.search(r"#(\d+)", details or "")
    return int(match.group(1)) if match else None


def _extract_code_block(details: str) -> Optional[str]:
    """Extract ```lean ... ``` code block from task details."""
    match = re.search(r"```lean\s*\n(.*?)```", details or "", re.DOTALL)
    return match.group(1).strip() if match else None


def _extract_claim_name(details: str) -> Optional[str]:
    """Extract axiom/theorem name to replace from details."""
    match = re.search(r"Replace:\s*`?(\w+)`?", details or "")
    return match.group(1) if match else None


def _apply_proof_patch(content: str, axiom_name: str, proof_code: str) -> Optional[str]:
    """Replace an axiom declaration with a theorem + proof."""
    # Match: axiom axiom_name : ...
    pattern = rf"^axiom\s+{re.escape(axiom_name)}\s*[:\n].*?(?=\n\n|\Z)"
    match = re.search(pattern, content, re.MULTILINE | re.DOTALL)
    if not match:
        return None
    return content[:match.start()] + proof_code + content[match.end():]


# ─────────────────────────────────────────────
# Standalone test
# ─────────────────────────────────────────────

if __name__ == "__main__":
    import sys

    if "--test-build" in sys.argv:
        print("Running test build...")
        from dataclasses import dataclass as dc

        @dc
        class MockTask:
            task_id: str = "TEST-001"
            description: str = "Test build"
            details: str = ""

        success, summary = handle_lean_build(MockTask())
        print(f"Result: {'SUCCESS' if success else 'FAILED'}")
        print(f"Summary: {summary}")
    else:
        print("Usage: python3 lean_build_agent.py --test-build")
        print("Normally imported by physics_agent.py, not run directly.")
