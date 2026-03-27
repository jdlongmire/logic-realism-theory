# LRT Pre-Commit Checklist

Run this checklist before any commit that touches theory files (002, traceability, formalization, READMEs). Not every item applies to every commit — use the "When" column to determine relevance.

---

## 1. Build Verification

| Check | Command | When |
|-------|---------|------|
| Lean compiles clean | `cd formalization && ./scripts/build.sh` | Any formalization change |
| Zero sorries | `grep -r "sorry" LrtFormalization/ --include="*.lean" \| grep -v ".lake" \| grep -v "no sorry" \| wc -l` | Any formalization change |
| Axiom count matches paper | `grep -rh "^axiom" LrtFormalization/ --include="*.lean" \| wc -l` — compare to 002 prose | Any change to 002 or formalization |

---

## 2. Paper Internal Consistency (002)

| Check | Method | When |
|-------|--------|------|
| OPN/EXT numbering matches traceability | Compare 002 OPN-XXX/EXT-XXX references against `traceability/claims/` | Any 002 or traceability change |
| Epistemic status labels accurate | Verify ESTABLISHED/ARGUED/CONJECTURED/IMPORTED on each step | Any 002 derivation change |
| Dependency chains stated correctly | Each step cites its actual inputs | Any 002 derivation change |
| Step count matches | 002 header/abstract says N steps; body has N steps | Structural 002 changes |

---

## 3. Traceability

| Check | Command | When |
|-------|---------|------|
| Index matches paper numbering | Read `traceability/index.yaml` against 002 claims | Any 002 or traceability change |
| Reports regenerate clean | `cd traceability && python3 scripts/build.py --all` | Any traceability change |
| No orphan dependencies | Check `generated/risk-report.md` for broken refs | After regeneration |
| Claim count recorded | Note total in commit message if changed | Traceability changes |

---

## 4. READMEs

| Check | Files | When |
|-------|-------|------|
| Axiom count accurate | `README.md`, `formalization/README.md` | Axiom count changes |
| Step count accurate | `theory/README.md` | Step additions/removals |
| File path references valid | All three READMEs | File renames or moves |
| EXTERNAL/REMAINING breakdown correct | `README.md`, `formalization/README.md` | Axiom reclassification |

---

## 5. Supplements & Cross-References

| Check | Method | When |
|-------|--------|------|
| Referenced supplements exist | 002 cites S2, S13, S14, etc. — verify paths in `theory/supplementary/` | New supplement references |
| 001/002/003 don't contradict | Spot-check shared primitives (X, L₃, I∞, A) across all three | Changes to any theory file |
| Figures referenced correctly | Check `figures/` paths in 002 | Figure changes |

---

## 6. GitHub Issues & Projects

| Check | Command | When |
|-------|---------|------|
| Open issues reflect current state | `gh issue list -R jdlongmire/logic-realism-theory` | Major status changes (OPN resolved, step completed) |
| Project #3 (Research Program) current | `gh project item-list 3 --owner jdlongmire` | Done items marked, new items added |
| Project #4 (Cosmology) current | `gh project item-list 4 --owner jdlongmire` | Cosmology changes |

---

## 7. LRT Memory

| Check | Method | When |
|-------|--------|------|
| Axiom count in memory matches | Read ThinxS `memory/lrt_theory.md` | Axiom changes |
| OPN statuses current | Compare memory OPN table to 002 | OPN status changes |
| Traceability claim count current | Check memory vs actual | Traceability changes |
| MEMORY.md quick-reference line | `MEMORY.md` LRT section says correct axiom count | Axiom changes |

---

## Quick-Run Summary

For a typical 002 + traceability commit:

```bash
# 1. Build
cd /media/jdlongmire/Macro-Drive-2TB/GitHub_Repos/logic-realism-theory/formalization
grep -r "sorry" LrtFormalization/ --include="*.lean" | grep -v ".lake" | grep -v "no sorry" | wc -l
grep -rh "^axiom" LrtFormalization/ --include="*.lean" | wc -l

# 2. Traceability
cd ../traceability
python3 scripts/build.py --all

# 3. Cross-check
# - 002 OPN/EXT numbers match traceability index
# - README axiom counts match
# - GitHub projects reflect current state
# - LRT memory updated
```

---

## Governance

This checklist is referenced by the ThinX-Physics mode (`/mode physics`). When physics mode is active and a commit is requested, the agent runs applicable checklist items before staging files.
