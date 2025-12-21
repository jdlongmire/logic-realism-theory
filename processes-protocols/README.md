# Processes & Protocols

Documentation for AI-assisted theory development workflow.

---

## Contents

| Document | Purpose | When to Use |
|----------|---------|-------------|
| **AI_METHODOLOGY.md** | 10-phase development process | Session planning, understanding workflow |
| **SANITY_CHECK_PROTOCOL.md** | Verification checklist | After completing any track or major claim |
| **DEVELOPMENT_GUIDE.md** | Architecture, commands, workflows | Reference for repo structure, commands |
| **peer_review_protocol.md** | LLM-based review prompts | Pre-submission quality assurance |
| **reference_validation/** | Citation verification protocol | Verifying bibliographic accuracy |

---

## Quick Reference

### Before Claiming "Complete"
Run `SANITY_CHECK_PROTOCOL.md` - 9 checks covering build, proofs, imports, axioms, circularity, tone.

### Development Workflow
See `AI_METHODOLOGY.md` for the 10-phase process:
1. Initial Development (Claude Code)
2. Multi-LLM Adversarial Review
3. Human Review and Decision
4. Iteration Until Verified
5. Repository Documentation
6. SME Pre-Review
7. Formal Verification (Lean 4)
8. Final Polish
9. Peer Review Submission
10. Experimental Validation

### Pre-Submission Review
Use `peer_review_protocol.md` prompts with multiple LLMs (Claude, GPT, Gemini, Grok) before journal submission.

---

## Related Documentation

- `AI-Collaboration-Profile.json` (root) - General collaboration stance
- `LRT-Collaboration-Addendum.md` (root) - LRT-specific protocols
- `lean/BEST_PRACTICES.md` - Lean 4 proof development
