# Generate PDF for Logic Field Theory Paper

## Method 1: Browser (Easiest - Recommended)

1. **Open the HTML file**:
   - Navigate to `paper/Logic_Field_Theory_Logic_Realism.html`
   - Double-click to open in your default browser
   - **IMPORTANT**: Wait 3-5 seconds for MathJax to fully load and render all mathematical formulas
   - Verify that tables are displaying properly as formatted tables (not compressed lines)
   - Verify that mathematical symbols (like |V_K|, N = 2^n) are properly formatted

2. **Print to PDF**:
   - Press `Ctrl+P` (Windows/Linux) or `Cmd+P` (Mac)
   - Select "Save as PDF" or "Microsoft Print to PDF" as printer
   - **Recommended settings**:
     - Layout: Portrait
     - Margins: Default
     - Background graphics: ON (to preserve styling and table borders)
     - Headers and footers: OFF
     - Scale: 100% (do not shrink to fit)
   - Click "Save" or "Print"
   - Save as: `Logic_Field_Theory_Logic_Realism.pdf`

3. **Verify the PDF**:
   - Open the generated PDF
   - Check that Section 3.6.1 table (Path-Based Systems) displays as proper table with rows/columns
   - Check that Section 3.6.2 table (Qubit Systems) displays as proper table with rows/columns
   - Check that all mathematical notation is properly rendered

**Result**: High-quality PDF with table of contents, proper tables, LaTeX math formatting, and styling preserved

## Method 2: Pandoc with LaTeX (If LaTeX installed)

```bash
cd paper
pandoc Logic_Realism_Foundational_Paper.md -o Logic_Field_Theory_Logic_Realism.pdf \
  --pdf-engine=pdflatex \
  --variable=geometry:margin=1in \
  --variable=documentclass:article \
  --variable=fontsize:11pt \
  --variable=colorlinks:true \
  --table-of-contents \
  --number-sections
```

**Requirements**:
- Pandoc (already installed at `/c/Program Files/Pandoc/pandoc`)
- LaTeX distribution (MiKTeX or TeX Live) - **Not currently installed**

To install MiKTeX: https://miktex.org/download

## Method 3: Online Conversion

1. Upload `Logic_Realism_Foundational_Paper.md` to https://www.markdowntopdf.com/
2. Download the generated PDF
3. Save as `Logic_Field_Theory_Logic_Realism.pdf`

---

**Recommended**: Use Method 1 (Browser) - it's fastest and preserves all formatting from the HTML version.
