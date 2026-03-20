# LRT Documentation

This directory contains all documentation for Logic Realism Theory, organized for both web publication (Jekyll/GitHub Pages) and developer reference.

## Directory Structure

```
docs/
├── articles/              # Expository articles and blog-style content
├── assets/                # Images, CSS, and static assets
├── formalization/         # Lean formalization research and documentation
├── papers/                # Technical papers (see index.md for listing)
├── topics/                # Topic-based reference pages
├── traceability/          # -> symlink to /traceability/generated/
├── _includes/             # Jekyll includes
├── _layouts/              # Jekyll layouts
├── index.md               # Main site landing page
├── definitions.md         # Glossary and key definitions
├── cite.md                # Citation information
└── README.md              # This file
```

## Subdirectories

### papers/
Technical papers presenting LRT derivations and results:
- Born rule derivation
- Hilbert space derivation
- QFT statistics
- GR extension
- Information Circulation Hypothesis papers

See [papers/index.md](papers/index.md) for the full listing.

### articles/
Expository articles for broader audiences:
- From logic to physics
- Common objections
- EPR resolution
- Empirical pillar

### topics/
Reference pages organized by topic:
- Born rule, Hilbert space, entanglement
- L3 constraints, measurement problem
- One-world realism, vehicle-content distinction

### formalization/
Documentation from the Lean formalization effort:
- **Research analyses**: moretti-oppio, torres-alegre, fiorentino-weigert, etc.
- **Subsumption studies**: MWI, categorical QM, einselection
- **AI consultations**: step3, K=2, actualization
- **Axiom status**: Current axiom inventory and audit reports
- **Work plans**: Active formalization priorities

### traceability/
Symlink to `/traceability/generated/` containing:
- claims.json - Structured claim database
- coverage-report.md - Proof coverage analysis
- dependency-graph.json/.mmd - Claim dependencies
- risk-report.md - Outstanding risks

## Building the Site

The docs/ directory is configured for Jekyll with GitHub Pages:

```bash
# Local development
cd docs
bundle install
bundle exec jekyll serve

# Or just push to GitHub and enable Pages on the repository
```

## Cross-References

- Active theory documents: `/theory/`
- Lean source code: `/formalization/LrtFormalization/`
- Traceability infrastructure: `/traceability/`
- Archives: `/archive/`
