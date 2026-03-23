"""
physics_agent.py patch — add lean_build and lean_proof dispatch.

Insert the following into physics_agent.py:

1. After the imports block, add:
   from lean_build_agent import handle_lean_build, handle_lean_proof

2. Replace the process_task() function body with the version below
   (adds dispatch before falling through to the existing Claude CLI path).
"""

# ─────────────────────────────────────────────────────────────────────────────
# PATCH: Add to imports section of physics_agent.py
# ─────────────────────────────────────────────────────────────────────────────

IMPORT_ADDITION = """
# Lean build integration
try:
    from lean_build_agent import handle_lean_build, handle_lean_proof
    LEAN_AGENT_AVAILABLE = True
except ImportError:
    LEAN_AGENT_AVAILABLE = False
    logger.warning("lean_build_agent.py not found — lean_build/lean_proof tasks will fail gracefully")
"""

# ─────────────────────────────────────────────────────────────────────────────
# PATCH: Replace process_task() in physics_agent.py
# Add lean dispatch before existing Claude CLI logic
# ─────────────────────────────────────────────────────────────────────────────

PROCESS_TASK_ADDITION = """
def process_task(task: Task) -> TaskResult:
    \"\"\"Process a single task with retry logic.\"\"\"
    logger.info(f"Processing: {task.task_id} - {task.description}")

    result = TaskResult(task=task, status=TaskStatus.RUNNING)
    start_time = time.time()

    # ── Lean task dispatch (no Claude CLI needed) ──────────────────────────
    if task.task_type in ("lean_build", "lean_proof") and LEAN_AGENT_AVAILABLE:
        try:
            if task.task_type == "lean_build":
                success, output = handle_lean_build(task)
            else:
                success, output = handle_lean_proof(task)

            result.duration = time.time() - start_time
            result.output = output

            if success:
                result.status = TaskStatus.SUCCESS
                if mark_task_complete(task):
                    logger.info(f"Lean task {task.task_id} completed ({result.duration:.1f}s)")
                else:
                    logger.warning(f"Lean task {task.task_id} done but failed to update tasks.md")
            else:
                result.status = TaskStatus.FAILED
                logger.warning(f"Lean task {task.task_id} failed: {output[:200]}")

            send_task_notification(result)
            return result

        except Exception as e:
            result.status = TaskStatus.FAILED
            result.output = f"Lean agent exception: {e}"
            result.duration = time.time() - start_time
            logger.error(f"Lean agent error for {task.task_id}: {e}")
            send_task_notification(result)
            return result

    elif task.task_type in ("lean_build", "lean_proof") and not LEAN_AGENT_AVAILABLE:
        result.status = TaskStatus.FAILED
        result.output = "lean_build_agent.py not available"
        result.duration = time.time() - start_time
        send_task_notification(result)
        return result

    # ── Standard Claude CLI path (supplements, derivations, etc.) ─────────
    for attempt in range(MAX_RETRIES + 1):
        if shutdown_requested:
            result.status = TaskStatus.FAILED
            result.output = "Shutdown requested"
            break

        if attempt > 0:
            logger.info(f"Retry {attempt}/{MAX_RETRIES} for {task.task_id}")
            time.sleep(RETRY_DELAY)

        result.retry_count = attempt
        prompt = build_physics_prompt(task)
        success, output = run_claude(prompt, LRT_REPO)
        result.output = output
        result.duration = time.time() - start_time

        if success:
            result.status = TaskStatus.SUCCESS
            target_path = LRT_REPO / "theory" / task.target
            result.file_created = target_path.exists()

            if mark_task_complete(task):
                logger.info(f"Task {task.task_id} completed successfully ({result.duration:.1f}s)")
            else:
                logger.warning(f"Task {task.task_id} completed but failed to update tasks.md")
            break
        elif "timed out" in output.lower():
            result.status = TaskStatus.TIMEOUT
            logger.warning(f"Task {task.task_id} timed out")
        else:
            result.status = TaskStatus.FAILED
            logger.warning(f"Task {task.task_id} attempt {attempt + 1} failed")

    send_task_notification(result)
    return result
"""
