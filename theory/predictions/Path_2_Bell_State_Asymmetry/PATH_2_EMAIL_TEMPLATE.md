# Path 2 Collaboration Outreach - Email Templates

**Version**: 1.0 | **Date**: November 2025

---

## Template 1: Initial Contact (IBM Quantum / Academic Labs)

**Subject**: Collaboration Opportunity: Novel Bell State Decoherence Test (1-2 Month Timeline)

**To**: [Principal Investigator / Lab Director]

Dear Dr. [Last Name],

I'm reaching out regarding a collaboration opportunity to test a novel quantum measurement prediction on [IBM Quantum / your trapped-ion system / your superconducting qubit platform].

**The Experiment**: We've identified a measurable asymmetry in Bell state decoherence rates (ΔT2/T1 ≈ 0.19) that standard quantum mechanics does not predict. This test has:

- **High confidence**: 12σ signal-to-noise ratio (strongest prediction in our framework)
- **Fast timeline**: 1-2 months from platform access to results
- **Low resources**: ~8,000 circuit shots on existing hardware
- **Clear outcome**: Publishable result (PRL-quality) regardless of whether prediction is confirmed or falsified

**What Makes This Attractive**:
- Uses existing quantum computers (IBM Quantum,IonQ, etc.) - no custom equipment
- 3-point measurement design with built-in systematic error checks
- Decision tree protocol allows early termination if initial results are null
- Computational validation complete (Jupyter notebook, QuTiP simulations)
- Experimental protocol ready for review

**Materials Available**:
- 1-page summary (non-technical overview)
- 2-page technical summary (detailed procedures for experimentalists)
- Full protocol (PATH_2_PILOT_TEST_PROTOCOL.md, ~450 lines)
- Computational notebook (first-principles derivation + simulation)

**Next Steps**:
Would you be open to a 30-minute Zoom call to discuss feasibility on your platform? I can share the technical materials in advance for your team to review.

Alternatively, if you'd prefer to review the materials first, I'm happy to send the 1-page summary and we can schedule a call if it looks interesting.

**Timeline**:
- **This month**: Platform access + calibration
- **Next month**: Execute 3-point pilot test
- **Month 3**: Analysis + manuscript preparation (co-authored)

Thank you for considering this opportunity. I look forward to hearing from you.

Best regards,
James D. Longmire

**GitHub Repository**: logic-realism-theory (all materials publicly available, MIT License)
**Materials Request**: Reply to this email and I'll send the 1-page summary + technical details

---

## Template 2: Follow-Up (After 1 Week)

**Subject**: Re: Collaboration Opportunity - Bell State Decoherence Test

Dear Dr. [Last Name],

I wanted to follow up on my previous email regarding the Bell state decoherence asymmetry experiment.

I understand you're likely very busy, so I've attached a 1-page summary that gives a quick overview of the experiment, timeline, and resource requirements.

**Key Points**:
- **Time commitment**: ~2 hours for initial pilot test (Point 1), then decision on whether to proceed
- **Resource ask**: IBM Quantum access (Premium or collaboration) OR academic platform with T1>100μs
- **Deliverable**: Co-authored publication (PRL target), shared credit

If this doesn't fit with your current research priorities, I completely understand. Alternatively, if you know of other groups who might be interested in quantum measurement tests, I'd appreciate any referrals.

Thank you again for your time.

Best regards,
James D. Longmire

**Attachments**:
- PATH_2_ONE_PAGE_SUMMARY.md (1 page)
- PATH_2_TECHNICAL_SUMMARY.md (2 pages, for experimentalist review)

---

## Template 3: Technical Deep Dive (After Initial Interest)

**Subject**: Technical Materials - Bell State Decoherence Test

Dear Dr. [Last Name],

Thank you for your interest in the Bell state asymmetry experiment! As requested, here are the detailed technical materials:

**Protocol Document** (PATH_2_PILOT_TEST_PROTOCOL.md):
- 3-point measurement design (Baseline + Validation + Null Test)
- Detailed circuit specifications (gate counts, depth, shot requirements)
- Decision tree protocol (GO/NO-GO criteria)
- Timeline and resource estimates
- Risk mitigation strategies

**Computational Notebook** (bell_asymmetry_first_principles.ipynb):
- Part 1: Variational framework (η derivation from first principles)
- Part 2: Fisher information calculation and LRT prediction
- Part 3: QuTiP 2-qubit master equation simulation
- Results: ΔT2/T1 predicted = 0.193, simulated = 0.241 (25% error)

**Technical Summary** (PATH_2_TECHNICAL_SUMMARY.md):
- Detailed measurement procedures (T1, T2 extraction methods)
- Platform requirements (IBM Quantum, IonQ specifications)
- Data analysis pipeline (software stack, error propagation)
- FAQ section

**Qubit Requirements** (for your platform check):
- T1 > 100 μs, T2 > 50 μs (minimum for 20-point measurement)
- Direct 2-qubit coupling (avoid SWAP gates)
- Gate fidelity: Single-qubit < 0.1% error, two-qubit < 1% error
- Readout fidelity > 95%

**Next Steps**:
1. Review protocol with your experimentalists
2. Check if your platform meets qubit requirements (I can help with calibration data analysis)
3. Schedule Zoom call to discuss collaboration model (co-authorship, timeline, resource allocation)
4. If feasible: Draft collaboration agreement and begin Week 1-2 (platform access + calibration)

**Questions I Can Answer**:
- Platform-specific adaptations (IBM vs IonQ vs Google vs academic setups)
- Error budget analysis (what precision is achievable on your system?)
- Alternative measurement sequences (T2* vs Hahn echo, dynamical decoupling options)
- Collaboration models (co-authorship agreements, IP, open data policies)

Please let me know if you have any questions or need clarification on any aspect of the protocol. I'm happy to jump on a call at your convenience.

Looking forward to working together!

Best regards,
James D. Longmire

**Links**:
- GitHub Repository: [provide URL]
- Computational Notebook (executed): [direct link to .ipynb file]
- Protocol (full): [direct link to .md file]

---

## Template 4: Collaboration Agreement Draft (After Technical Review)

**Subject**: Collaboration Agreement - Bell State Asymmetry Pilot Test

Dear Dr. [Last Name],

Thank you for the productive discussion on [date]. I'm excited to move forward with the collaboration! Here's a draft agreement based on our conversation:

**Collaboration Scope**:
- **Pilot Test** (1-2 months): Execute 3-point measurement design on [IBM Quantum / your platform]
- **Resource Commitment**:
  - Theory team: Protocol design ✅, analysis code, data interpretation, manuscript writing
  - Experimental team: Platform access, circuit execution (8,000-12,000 shots), calibration data
- **Timeline**:
  - Week 1-2: Platform access + Bell state calibration
  - Week 3-4: Baseline measurement (Point 1) + decision tree
  - Week 5-6: Validation (Point 2) + null test (Point 3) [if Point 1 successful]
  - Week 7-8: Analysis + manuscript preparation

**Authorship Agreement**:
- **Co-authorship**: Joint publication with shared credit
- **Author Order**: [To be determined based on contribution - discuss]
- **Corresponding Author**: [Discuss preference]
- **Acknowledgments**: Funding sources, platform providers

**Publication Plan**:
- **Primary Target**: Physical Review Letters (PRL)
- **Backup Targets**: PRX Quantum, Nature Physics
- **Preprint**: arXiv submission after pilot test complete (regardless of result)
- **Data/Code**: Open access (Zenodo/GitHub, MIT License)

**IP and Licensing**:
- No patents, open science model
- Code and data: MIT License (publicly available)
- Publication: Standard academic copyright (journal-dependent)

**Decision Points**:
- After Point 1 (Baseline): GO/NO-GO for Points 2-3 based on decision tree
- After Point 3 (Null Test): GO/NO-GO for full study (100+ circuits)
- Either party can terminate with 1-week notice if technical issues arise

**Confidentiality**:
- Results remain confidential until preprint submission
- Platform-specific technical details can be anonymized if requested

**Next Steps**:
1. Review and suggest edits to this agreement
2. Finalize author list and contribution statements
3. Begin Week 1: Platform access setup
4. Schedule weekly check-ins during 8-week pilot test

Does this agreement align with your expectations? Please suggest any modifications.

Best regards,
James D. Longmire

**Attached**: Collaboration agreement (editable Google Doc / Word doc)

---

## Template 5: Referral Request (If Group Declines)

**Subject**: Referral Request - Quantum Measurement Collaboration

Dear Dr. [Last Name],

Thank you for considering the Bell state decoherence test. I completely understand that it doesn't fit with your current research priorities.

If you know of other experimental groups who might be interested in testing novel quantum measurement predictions, I'd greatly appreciate any referrals. Specifically, I'm looking for groups with:

- IBM Quantum access (Premium or academic collaboration)
- IonQ / trapped-ion platforms
- Superconducting qubit platforms (academic labs with T1>100μs)
- Interest in quantum foundations / measurement theory

**Why This Might Interest Them**:
- High-impact result potential (PRL-quality)
- Fast timeline (1-2 months, not years)
- Low resource commitment (pilot test = 2 hours)
- Publishable regardless of outcome

If you could forward this email to colleagues or suggest specific PIs, that would be incredibly helpful.

Thank you again for your time and consideration.

Best regards,
James D. Longmire

**Materials Available**: 1-page summary, technical protocol, computational notebook

---

## Template 6: Gratitude + Next Steps (After Successful Collaboration)

**Subject**: Thank You - Bell State Results + Next Steps

Dear Dr. [Last Name] and Team,

Thank you for the excellent collaboration on the Bell state decoherence pilot test! The results are [promising/interesting/null but valuable - adapt based on outcome], and I'm excited to move forward with [manuscript preparation / full study / theory revision].

**Results Summary**: [Attach brief 1-paragraph summary of ΔT2/T1 measurement + significance]

**Next Steps**:
1. **Data Archive**: Prepare dataset for Zenodo (I'll create the repository)
2. **Manuscript Draft**: I'll prepare the first draft by [date] and share for your feedback
3. **Figures**: Publication-quality versions (I'll generate these using Matplotlib)
4. **Supplementary Info**: Detailed methods, calibration data, analysis code

**Timeline to Submission**:
- Draft circulated: [2 weeks from now]
- Revisions: [1 week]
- arXiv preprint: [3 weeks from now]
- Journal submission (PRL): [4 weeks from now]

**Acknowledgments**: Please send:
- Full author list with affiliations
- Funding acknowledgments
- Platform acknowledgment text (how you'd like to cite IBM Quantum / your lab)

Looking forward to seeing this published!

Best regards,
James D. Longmire

**Attached**: Preliminary results figure (draft for manuscript)

---

## Customization Notes

**For IBM Quantum Contacts**:
- Emphasize: Demonstrates novel use case for IBM hardware, publishable in 1-2 months
- Value prop: PR for IBM Quantum if result is positive, helps demonstrate research capability of platform

**For Academic Labs**:
- Emphasize: Co-authorship on high-impact publication, low resource commitment
- Value prop: Complements existing research, doesn't require new equipment

**For IonQ Contacts**:
- Emphasize: Cross-platform validation (after IBM baseline measurement)
- Value prop: Shows universality of quantum measurement physics, platform-independent result

**For Experimentalists (vs PIs)**:
- Lead with technical details (2-page summary first)
- Focus on: Circuit specs, shot requirements, calibration needs
- Value prop: Interesting physics, clear measurement protocol, analysis tools provided

**For PIs**:
- Lead with high-level summary (1-page)
- Focus on: Publication potential, timeline, resource efficiency
- Value prop: Low-risk, high-reward collaboration opportunity

---

**Usage Instructions**:
1. Select appropriate template based on recipient and stage of outreach
2. Customize [bracketed fields] with specific names, dates, platform details
3. Attach relevant materials (1-page summary, technical summary, protocol)
4. Follow up after 1 week if no response (Template 2)
5. Track outreach in contact list (see PATH_2_CONTACT_LIST.md)
