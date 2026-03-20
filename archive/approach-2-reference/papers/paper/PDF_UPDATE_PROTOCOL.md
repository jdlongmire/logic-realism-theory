# PDF Update Protocol

## General Rule

**For ANY paper where we maintain a PDF version**: When the markdown source is updated, the PDF MUST be regenerated to stay synchronized.

## Current Papers with PDFs

1. **Logic_Realism_Foundational_Paper.md** → `Logic_Field_Theory_Logic_Realism.pdf`
   - Source: `Logic_Realism_Foundational_Paper.md`
   - HTML intermediate: `Logic_Field_Theory_Logic_Realism.html`
   - PDF output: `Logic_Field_Theory_Logic_Realism.pdf`

2. **Logic_Field_Theory_I_Quantum_Probability.md** → `Logic_Field_Theory_I_Quantum_Probability.pdf`
   - Source: `Logic_Field_Theory_I_Quantum_Probability.md`
   - PDF output: (if exists, must be updated when source changes)

## PDF Regeneration Methods

### Method 1: Browser Print to PDF (Recommended - No LaTeX required)

**Use when**: LaTeX is not installed on the system

**Steps**:
1. Regenerate HTML from updated markdown:
   ```bash
   cd paper
   pandoc [SOURCE].md -o [OUTPUT].html \
     --standalone \
     --table-of-contents \
     --number-sections \
     --mathjax \
     --css=https://cdn.jsdelivr.net/npm/water.css@2/out/water.css \
     --metadata title="[TITLE]"
   ```

2. Open HTML in browser
3. **Wait 3-5 seconds** for MathJax to render all mathematical formulas
4. Verify content is correct (check recent changes)
5. Print to PDF:
   - Press `Ctrl+P` (Windows/Linux) or `Cmd+P` (Mac)
   - Select "Save as PDF" or "Microsoft Print to PDF"
   - Settings:
     - Background graphics: **ON**
     - Headers/footers: **OFF**
     - Scale: **100%**
   - Save as `[OUTPUT].pdf`

### Method 2: Pandoc with LaTeX (If LaTeX installed)

**Use when**: LaTeX (MiKTeX or TeX Live) is installed

**Steps**:
```bash
cd paper
pandoc [SOURCE].md -o [OUTPUT].pdf \
  --pdf-engine=pdflatex \
  --variable=geometry:margin=1in \
  --variable=documentclass:article \
  --variable=fontsize:11pt \
  --variable=colorlinks:true \
  --table-of-contents \
  --number-sections
```

### Method 3: Online Conversion (Fallback)

**Use when**: Neither Method 1 nor 2 is convenient

**Steps**:
1. Upload markdown to https://www.markdowntopdf.com/
2. Download generated PDF
3. Save with correct filename

## Verification Checklist

Before committing PDF updates:

- [ ] PDF filename matches expected output name
- [ ] Table of contents is present and correct
- [ ] Mathematical formulas render correctly (not raw LaTeX)
- [ ] Tables display properly (not compressed lines)
- [ ] Recent changes from markdown are visible in PDF
- [ ] File size is reasonable (~1-3 MB for typical papers)

## Git Workflow

**When updating papers**:
1. Edit markdown source
2. Regenerate HTML (if using browser method)
3. **IMMEDIATELY regenerate PDF**
4. Stage all three files together:
   ```bash
   git add paper/[SOURCE].md paper/[OUTPUT].html paper/[OUTPUT].pdf
   ```
5. Commit with clear message indicating PDF was updated

**Example**:
```bash
git add paper/Logic_Realism_Foundational_Paper.md \
        paper/Logic_Field_Theory_Logic_Realism.html \
        paper/Logic_Field_Theory_Logic_Realism.pdf

git commit -m "Update Logic Realism paper: [description]

- Markdown: [changes made]
- HTML: Regenerated
- PDF: Regenerated from updated HTML

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>"
```

## Common Issues

### Issue: PDF shows old content
**Cause**: Forgot to regenerate PDF after markdown changes
**Fix**: Follow regeneration steps above, verify changes visible before saving

### Issue: Math formulas show as raw LaTeX in PDF
**Cause**: Didn't wait for MathJax to render (browser method)
**Fix**: Wait 3-5 seconds after opening HTML, refresh if needed

### Issue: Tables compressed into single line
**Cause**: Markdown table syntax issues or pipe characters in headers
**Fix**: Use `$\|V_K\|$` instead of `|V_K|` in table headers, check table formatting

### Issue: PDF file size is very large (>10 MB)
**Cause**: High-resolution images or embedded fonts
**Fix**: Optimize images, or use Method 2 (LaTeX) for better compression

## Automation (Future)

**TODO**: Create script to automate full pipeline:
- Detect markdown changes
- Regenerate HTML
- Trigger PDF generation
- Verify output quality
- Stage files for commit

Until then: **Manual PDF regeneration is REQUIRED for every paper update.**

---

**Last Updated**: October 7, 2025
**Status**: Active protocol for all paper PDFs in repository
