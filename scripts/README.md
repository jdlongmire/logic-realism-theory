# LRT Scripts

Automation and integration scripts for the Logic Realism Theory research program.

---

## Integration Architecture

```
┌───────────────────────────────────────────────────────┐
│              PERPLEXITY COMPUTER (remote)              │
│  - Reads repo via GitHub API                          │
│  - Drafts Lean proof attempts                         │
│  - Runs MMR adversarial reviews                       │
│  - Queues tasks → theory/tasks.md                     │
│  - Reads build reports from docs/formalization/       │
│    build-reports/LATEST.md                            │
└────────────────────┬──────────────────────────────────┘
                     │  GitHub (tasks.md, commits, issues)
                     ▼
┌───────────────────────────────────────────────────────┐
│              THINXS (local machine)                    │
│  physics_agent.py  polls theory/tasks.md every 5 min  │
│       ↓ dispatch                                      │
│  lean_build_agent.py  (this repo: scripts/)           │
│  - lean_build tasks → lake build → report → commit    │
│  - lean_proof tasks → apply → validate → commit/roll  │
└───────────────────────────────────────────────────────┘
```

---

## Scripts

### `lean_build_agent.py`
Lean CI integration. Called by ThinxS `physics_agent.py` for `lean_build`
and `lean_proof` task types.

**lean_build** — full `lake build`:
- Fetches Mathlib cache
- Runs `lake build`, parses axiom/sorry counts
- Writes structured Markdown report to `docs/formalization/build-reports/`
- Posts summary to GitHub issue (if specified in task details)
- Commits report to repo

**lean_proof** — proof attempt validation:
- Applies Lean code from task details to target file
- Runs `lake build` on the affected module
- If success + 0 sorries: commits the change
- If failure: rolls back, posts error to GitHub issue

**Standalone test:**
```bash
cd logic-realism-theory
python3 scripts/lean_build_agent.py --test-build
```

### `physics_agent_patch.py`
Instructions for patching ThinxS `physics_agent.py` to dispatch
`lean_build` and `lean_proof` task types to `lean_build_agent.py`.

Apply once on your local ThinxS installation.

---

## Task Queue Protocol

Tasks are queued by Perplexity Computer in `theory/tasks.md`.
ThinxS `physics_agent.py` polls this file every 5 minutes.

### Task format

```markdown
- [ ] **LEAN-BUILD-001**: Run full Lean build and report results
  - Type: lean_build
  - Target: docs/formalization/build-reports/build-report-YYYYMMDD.md
  - Supports: <claim IDs>
  - Details: <context, issue number if any>

- [ ] **LEAN-PROOF-XXX**: Derive <axiom name> from Mathlib
  - Type: lean_proof
  - Target: formalization/LrtFormalization/StepN_Name.lean
  - Supports: <claim ID>
  - Details: Replace: `axiom_name`. Issue: #N.
    \```lean
    <proof code>
    \```
```

### Build reports

Reports are committed to `docs/formalization/build-reports/`.
`LATEST.md` always reflects the most recent build.
Perplexity Computer reads `LATEST.md` at session start to get current
axiom/sorry counts without needing to run a build.

---

## Setup (ThinxS local machine)

1. Ensure elan/lake is installed: `~/.elan/bin/lake`
2. Apply the physics_agent patch:
   ```bash
   # See scripts/physics_agent_patch.py for exact changes
   # Add to physics_agent.py imports:
   from scripts.lean_build_agent import handle_lean_build, handle_lean_proof
   ```
   Or run the patch script:
   ```bash
   python3 scripts/physics_agent_patch.py
   ```
3. Restart physics_agent daemon:
   ```bash
   python3 physics_agent.py --daemon
   ```

---

*HCAE — Human-Curated, AI-Enabled*
