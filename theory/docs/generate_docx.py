#!/usr/bin/env python3
"""
Generate properly formatted Word documents from LRT markdown sources.
Uses python-docx for proper Word tables instead of pandoc's pseudo-tables.
"""

import re
from pathlib import Path
from docx import Document
from docx.shared import Pt, Inches, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT
from docx.enum.style import WD_STYLE_TYPE
from docx.oxml.ns import qn
from docx.oxml import OxmlElement

# Paths
THEORY_DIR = Path(__file__).parent.parent
DOCS_DIR = Path(__file__).parent
FIGURES_DIR = THEORY_DIR / "figures"

def set_cell_shading(cell, color):
    """Set cell background color."""
    tc = cell._tc
    tcPr = tc.get_or_add_tcPr()
    shd = OxmlElement('w:shd')
    shd.set(qn('w:fill'), color)
    tcPr.append(shd)

def add_heading(doc, text, level):
    """Add a heading with proper style."""
    p = doc.add_heading(text, level=level)
    return p

def add_paragraph(doc, text, style='Normal'):
    """Add a paragraph with optional styling."""
    p = doc.add_paragraph(text, style=style)
    return p

def add_table(doc, headers, rows, header_color='4472C4'):
    """Add a properly formatted Word table."""
    table = doc.add_table(rows=1 + len(rows), cols=len(headers))
    table.style = 'Table Grid'
    table.alignment = WD_TABLE_ALIGNMENT.CENTER

    # Header row
    header_row = table.rows[0]
    for i, header in enumerate(headers):
        cell = header_row.cells[i]
        cell.text = header
        # Bold header text
        for paragraph in cell.paragraphs:
            for run in paragraph.runs:
                run.bold = True
        set_cell_shading(cell, header_color)
        # White text on blue background
        for paragraph in cell.paragraphs:
            for run in paragraph.runs:
                run.font.color.rgb = RGBColor(255, 255, 255)

    # Data rows
    for i, row_data in enumerate(rows):
        row = table.rows[i + 1]
        for j, cell_text in enumerate(row_data):
            row.cells[j].text = str(cell_text)
            # Alternate row shading
            if i % 2 == 1:
                set_cell_shading(row.cells[j], 'F2F2F2')

    doc.add_paragraph()  # Space after table
    return table

def parse_markdown_table(text):
    """Extract headers and rows from markdown table."""
    lines = [l.strip() for l in text.strip().split('\n') if l.strip()]
    if len(lines) < 2:
        return None, None

    # Parse header
    headers = [c.strip() for c in lines[0].split('|') if c.strip()]

    # Skip separator line (---|---|---)
    # Parse data rows
    rows = []
    for line in lines[2:]:
        cells = [c.strip() for c in line.split('|') if c.strip()]
        if cells:
            rows.append(cells)

    return headers, rows

def add_image_if_exists(doc, image_name, caption=None):
    """Add image if it exists in figures directory."""
    img_path = FIGURES_DIR / image_name
    if img_path.exists():
        try:
            doc.add_picture(str(img_path), width=Inches(5.5))
            last_para = doc.paragraphs[-1]
            last_para.alignment = WD_ALIGN_PARAGRAPH.CENTER
            if caption:
                cap = doc.add_paragraph(caption, style='Caption')
                cap.alignment = WD_ALIGN_PARAGRAPH.CENTER
            return True
        except Exception as e:
            print(f"Warning: Could not add image {image_name}: {e}")
    return False

def process_inline_formatting(paragraph, text):
    """Process bold, italic, and code formatting."""
    # Simple approach: handle basic patterns
    # For complex nested formatting, we'd need a proper parser

    # Replace LaTeX math with styled text
    text = re.sub(r'\$\$([^$]+)\$\$', r'[\1]', text)
    text = re.sub(r'\$([^$]+)\$', r'[\1]', text)

    # Split on bold markers and process
    parts = re.split(r'(\*\*[^*]+\*\*)', text)
    for part in parts:
        if part.startswith('**') and part.endswith('**'):
            run = paragraph.add_run(part[2:-2])
            run.bold = True
        elif part:
            # Handle italic within non-bold
            italic_parts = re.split(r'(\*[^*]+\*)', part)
            for ip in italic_parts:
                if ip.startswith('*') and ip.endswith('*') and not ip.startswith('**'):
                    run = paragraph.add_run(ip[1:-1])
                    run.italic = True
                elif ip:
                    # Handle code
                    code_parts = re.split(r'(`[^`]+`)', ip)
                    for cp in code_parts:
                        if cp.startswith('`') and cp.endswith('`'):
                            run = paragraph.add_run(cp[1:-1])
                            run.font.name = 'Consolas'
                        elif cp:
                            paragraph.add_run(cp)

def generate_tab_docx():
    """Generate TAB-v2.0.docx with proper formatting."""
    doc = Document()

    # Set document defaults
    style = doc.styles['Normal']
    style.font.name = 'Times New Roman'
    style.font.size = Pt(12)

    # Title
    title = doc.add_heading('The Actualization Bridge: Transcendental Foundations of Logic Realism Theory', 0)
    title.alignment = WD_ALIGN_PARAGRAPH.CENTER

    # Subtitle
    subtitle = doc.add_paragraph('Part I: Ontological Groundwork')
    subtitle.alignment = WD_ALIGN_PARAGRAPH.CENTER
    for run in subtitle.runs:
        run.italic = True
        run.font.size = Pt(14)

    # Author info
    doc.add_paragraph()
    author = doc.add_paragraph('James D. Longmire')
    author.alignment = WD_ALIGN_PARAGRAPH.CENTER
    affil = doc.add_paragraph('Northrop Grumman Fellow (unaffiliated research)')
    affil.alignment = WD_ALIGN_PARAGRAPH.CENTER
    orcid = doc.add_paragraph('ORCID: 0009-0009-1383-7698')
    orcid.alignment = WD_ALIGN_PARAGRAPH.CENTER

    doc.add_paragraph()
    doc.add_paragraph('─' * 50).alignment = WD_ALIGN_PARAGRAPH.CENTER

    # Abstract
    add_heading(doc, 'Abstract', 1)
    abstract_text = """This paper establishes the minimal ontological structure required for anything to exist. Beginning from the impossibility of derivation from absolute nothing, we argue that three primitives are jointly necessary and sufficient for the constitution of reality: prescriptive logical constraint (L₃), infinite informational possibility (I∞), and actualization (A). These primitives are not postulated but transcendentally derived as conditions for the possibility of determinate existence. Their interaction yields the core physics bridge of Logic Realism Theory: actuality coincides with the logically admissible informational configurations of the total possibility space. This result, expressed as A_Ω = L₃(I∞), provides the ontological ground from which physical structure can subsequently be reconstructed. The present paper develops no new physical formalisms; instead, it secures the ontological framework intended to underwrite subsequent formal reconstruction of quantum and spacetime structure."""
    add_paragraph(doc, abstract_text)

    kw = doc.add_paragraph()
    kw.add_run('Keywords: ').bold = True
    kw.add_run('logic, information ontology, metaphysics of reality, transcendental grounding')

    doc.add_paragraph('─' * 50).alignment = WD_ALIGN_PARAGRAPH.CENTER

    # Section 1
    add_heading(doc, '1. Three Guiding Observations', 1)
    add_paragraph(doc, 'The present argument begins from three observations about the structure of physical reality.')

    # Figure 1
    add_image_if_exists(doc, 'TAB-grounding-sequence.png',
                       'Figure 1: The complete grounding sequence. Guiding observations motivate the primitive ontology χ = [L₃ : I∞ : A], which grounds the actualized domain characterized by A_Ω = L₃(I∞).')

    # Section 1.1
    add_heading(doc, '1.1 Physical Reality Has an Origin', 2)
    add_paragraph(doc, 'Physical reality has an origin in something. The origin need not be temporal; it may be ontological. But the idea that the totality of what exists is simply brute and underived is unstable. Even the denial that reality has an origin presupposes some background structure in virtue of which the denial is meaningful.')
    add_paragraph(doc, 'This observation deepens into an impossibility argument. Absolute nothing (the complete absence of being, structure, constraint, and possibility) cannot generate or ground existence. This is not merely an empirical observation but a logical necessity: nothing has no properties, including the property of being able to produce something.')

    # Section 1.2
    add_heading(doc, '1.2 Physical Reality Is Logical, Informational, and Dynamic', 2)
    add_paragraph(doc, 'Our physical theories presuppose logical constraint: certain configurations are excluded as impossible. They describe systems through structured distinctions (states, fields, amplitudes) which are naturally interpreted as informational. And they encode change: systems evolve, transition, and actualize states.')

    # Section 1.3
    add_heading(doc, '1.3 No Actuality Violates the Fundamental Laws of Logic', 2)
    add_paragraph(doc, 'Apparent anomalies in physics never license genuine contradiction. Superposition, contextuality, and nonlocal correlations challenge classical intuitions, but they do not instantiate violations of identity, non-contradiction, or excluded middle. The working assumption of physics is that whatever is physically actual must be logically admissible.')

    # Section 1.4 with table
    add_heading(doc, '1.4 The Primitive Ontology and Two Core Results', 2)
    add_paragraph(doc, 'The three observations motivate three primitives:')

    add_table(doc,
              ['Observation', 'Primitive'],
              [
                  ['Reality has an origin', 'Ontological unity χ'],
                  ['Logical/informational/dynamic structure', 'L₃, I∞, A'],
                  ['No actuality violates logic', 'Bridge constraint']
              ])

    add_paragraph(doc, 'The primitives form a co-constitutive unity:')
    eq = doc.add_paragraph('χ ≡ [L₃ : I∞ : A]')
    eq.alignment = WD_ALIGN_PARAGRAPH.CENTER
    for run in eq.runs:
        run.italic = True
        run.font.size = Pt(14)

    add_paragraph(doc, 'The third observation yields the bridge equation: actuality coincides with the logically admissible configurations of the informational domain:')
    eq2 = doc.add_paragraph('A_Ω = L₃(I∞)')
    eq2.alignment = WD_ALIGN_PARAGRAPH.CENTER
    for run in eq2.runs:
        run.italic = True
        run.font.size = Pt(14)

    # Section 1.5 Division of Labor
    add_heading(doc, '1.5 Division of Labor: TAB and LRT-MASTER', 2)
    add_paragraph(doc, 'This paper (TAB, Part I) develops the ontological groundwork only: the transcendental argument for χ ≡ [L₃ : I∞ : A] and the bridge identity A_Ω = L₃(I∞). No physical formalisms are derived here.')
    add_paragraph(doc, 'The physics reconstruction proceeds in the companion paper (LRT-MASTER, Part II), which imports the bridge identity as its starting point and derives the full structure of non-relativistic quantum mechanics: complex Hilbert space, projection-valued measures, the Born rule, continuous time, and the Schrödinger equation.')

    # Section 2
    add_heading(doc, '2. Necessity of Logical Constraint (L₃)', 1)

    add_heading(doc, '2.1 The Prescriptive Character of Logic', 2)
    add_paragraph(doc, 'Logical constraint is not a description of how minds happen to think. It is a prescriptive structure governing what can and cannot obtain. The law of non-contradiction (a thing cannot both be and not be in the same respect at the same time) is not a psychological generalization but an ontological constraint.')

    add_heading(doc, '2.2 From Inference to Ontology', 2)
    add_paragraph(doc, 'A referee will rightly ask: why does the impossibility of asserting contradictions entail the impossibility of ontological contradiction? The bridge requires an additional step.')
    add_paragraph(doc, 'Determinate existence requires stable identity conditions. For something to be, it must be what it is and not something else. Contradictory states destroy identity conditions: if Px and not-Px hold simultaneously, x has no stable identity with respect to P. Such a state is not merely unthinkable; it is ontologically inadmissible. There is nothing for it to be.')

    add_heading(doc, '2.3 L₃ as Prescriptive Constraint Structure', 2)
    add_paragraph(doc, 'We designate the prescriptive logical constraint structure as L₃, signifying its triadic character: identity, non-contradiction, and excluded middle. These are not separate principles but aspects of a unified constraint on determinate being.')
    p = doc.add_paragraph()
    p.add_run('Identity: ').bold = True
    p.add_run('For any x, x = x. A thing is what it is.')
    p = doc.add_paragraph()
    p.add_run('Non-contradiction: ').bold = True
    p.add_run('For any x and property P, not (Px and not-Px) in the same respect at the same time.')
    p = doc.add_paragraph()
    p.add_run('Excluded middle: ').bold = True
    p.add_run('For any x and property P, either Px or not-Px.')

    add_heading(doc, '2.4 From Epistemic to Transcendental Necessity', 2)
    add_paragraph(doc, 'A careful distinction is required here between two types of necessity:')
    p = doc.add_paragraph()
    p.add_run('Epistemic necessity: ').bold = True
    p.add_run('We cannot coherently represent or reason about reality without presupposing L₃.')
    p = doc.add_paragraph()
    p.add_run('Transcendental necessity: ').bold = True
    p.add_run('L₃ is required for the possibility of any determinate being whatsoever.')
    add_paragraph(doc, 'The arguments above establish epistemic necessity directly. The skeptic cannot formulate their skepticism without invoking what they deny. But does this entail transcendental necessity? Could reality itself violate L₃ even if we cannot represent that possibility?')
    add_paragraph(doc, 'The answer is no, and the reason goes beyond mere representational limits. The argument from §2.2 establishes that determinate existence requires stable identity conditions. Contradictions do not merely evade our representation; they fail to constitute anything at all.')

    # Section 3
    add_heading(doc, '3. Necessity of Informational Domain (I∞)', 1)

    add_heading(doc, '3.1 The Requirement of Differentiation', 2)
    add_paragraph(doc, 'Existence is determinate existence. For anything to be actual, it must be this rather than that. Determinacy requires differentiation, and differentiation requires a domain of possible distinctions.')

    add_heading(doc, '3.2 Information as Structured Distinction', 2)
    add_paragraph(doc, 'We understand information in the fundamental sense as structured distinction. Information is not primarily about messages or signals (though these are derivative). It is about the possibility of distinguishing configurations.')

    add_heading(doc, '3.3 I∞ as Total Possibility Space', 2)
    add_paragraph(doc, 'We designate the total informational possibility space as I∞. The subscript signifies completeness rather than cardinality. This distinction matters: the argument does not claim that the possibility space is numerically infinite, but that it is complete with respect to possible distinctions.')

    # Section 4
    add_heading(doc, '4. Necessity of Actualization (A)', 1)

    add_heading(doc, '4.1 The Gap Between Possibility and Actuality', 2)
    add_paragraph(doc, 'L₃ and I∞ together provide logical constraint and a possibility space. But they do not yet account for actuality. Many configurations are logically consistent and informationally possible but do not obtain. Why these configurations rather than those?')

    add_heading(doc, '4.2 A as Primitive Marking', 2)
    add_paragraph(doc, 'We designate the actualization primitive as A. Its role is to mark configurations as obtaining. This marking is not explanatorily further reducible.')
    add_paragraph(doc, 'A critical distinction: actualization is ontologically primitive, not random. Randomness is a positive characteristic; it presupposes a probability distribution governing outcomes. A has no such characteristic. It is not that A "randomly chooses" configurations; rather, A is the primitive marking of obtaining, prior to any selection mechanism.')

    add_heading(doc, '4.3 The Ontological Status of A', 2)
    add_paragraph(doc, 'A is transcendentally necessary because without it, the gap between possibility and actuality cannot be bridged. L₃ constrains what can obtain. I∞ provides the domain of what might obtain. But neither makes anything actual. Actuality requires a primitive that is not reducible to constraint or possibility.')

    add_heading(doc, '4.4 A\'s Grounding Role and the Bridge Identity', 2)
    add_paragraph(doc, 'A potential objection arises from the bridge identity derived below: if A_Ω = L₃(I∞), has A disappeared from the resulting ontology? Is it explanatorily idle?')
    add_paragraph(doc, 'The answer requires distinguishing two questions:')
    add_paragraph(doc, '1. What is the structure of the actualized domain? The bridge identity answers: L₃(I∞). The structural profile of actuality coincides with the L₃-admissible configurations of I∞.')
    add_paragraph(doc, '2. Why is there an actualized domain at all? A answers: because actualization is a primitive fact. Without A, there would be a space of admissible configurations with no fact of the matter about which obtain.')

    # Section 5
    add_heading(doc, '5. Interaction of the Primitives', 1)

    add_heading(doc, '5.1 The Primitive Ontology', 2)
    add_paragraph(doc, 'We now have three primitives, each transcendentally necessary:')
    p = doc.add_paragraph()
    p.add_run('L₃: ').bold = True
    p.add_run('Prescriptive logical constraint structure')
    p = doc.add_paragraph()
    p.add_run('I∞: ').bold = True
    p.add_run('Total informational possibility space')
    p = doc.add_paragraph()
    p.add_run('A: ').bold = True
    p.add_run('Actualization primitive')

    add_paragraph(doc, 'We designate their unity as χ:')
    eq = doc.add_paragraph('χ ≡ [L₃ : I∞ : A]')
    eq.alignment = WD_ALIGN_PARAGRAPH.CENTER

    add_heading(doc, '5.2 Mutual Dependence', 2)
    add_paragraph(doc, 'L₃ without I∞ would be constraint on nothing—a structure with no domain to constrain. I∞ without L₃ would be an undifferentiated plenum with no internal structure—configurations would blur into one another without the possibility of distinction. A without both would have nothing to actualize and no principle distinguishing coherent from incoherent configurations.')

    add_heading(doc, '5.3 Non-Redundancy of the Primitive Set', 2)
    add_paragraph(doc, 'The mutual dependence argument establishes that the primitives require one another. A stronger claim is available: no proper subset of {L₃, I∞, A} suffices for determinate actuality.')

    # Section 6
    add_heading(doc, '6. The Bridge Argument', 1)

    add_heading(doc, '6.1 The Grounding Sequence', 2)
    add_paragraph(doc, 'We now present the core argument in three steps.')

    # Figure 2
    add_image_if_exists(doc, 'LRT-observation-primitive-map.png',
                       'Figure 2: The equations-only view. Three observations motivate three primitives, yielding the primitive ontology and bridge identity.')

    p = doc.add_paragraph()
    p.add_run('Step 1: The Primitive Ontology').bold = True
    eq = doc.add_paragraph('χ ≡ [L₃ : I∞ : A]')
    eq.alignment = WD_ALIGN_PARAGRAPH.CENTER

    p = doc.add_paragraph()
    p.add_run('Step 2: The Grounding Relation').bold = True
    eq = doc.add_paragraph('χ ⊢ A_Ω')
    eq.alignment = WD_ALIGN_PARAGRAPH.CENTER

    p = doc.add_paragraph()
    p.add_run('Step 3: The Bridge Identity').bold = True
    eq = doc.add_paragraph('A_Ω = L₃(I∞)')
    eq.alignment = WD_ALIGN_PARAGRAPH.CENTER

    add_heading(doc, '6.2 Status of the Bridge Equation', 2)
    add_paragraph(doc, 'The bridge equation is an argued metaphysical identity. It is not:')
    add_paragraph(doc, '• A definition: We are not stipulating that A_Ω means L₃(I∞). We are arguing that the structure of actuality, given the primitives, coincides with this characterization.')
    add_paragraph(doc, '• A formal theorem: The argument is transcendental, not axiomatic. Formal verification can establish the internal consistency of the derivation chain, but the metaphysical warrant comes from the transcendental arguments of Sections 2–4.')

    add_heading(doc, '6.3 The Bridge Lemma', 2)
    add_paragraph(doc, 'The physics reconstruction in Part II requires a specific connection between the ontological primitives established here and the operational constraints that generate quantum structure. This connection is summarized as the Bridge Lemma:')
    p = doc.add_paragraph()
    p.add_run('Bridge Lemma. ').bold = True
    p.add_run('If A_Ω = L₃(I∞), then any proposition about a configuration c ∈ A_Ω satisfies L₃. Satisfying L₃ requires determinate content, which requires operational distinguishability. Therefore, every physical proposition is operationally distinguishable.').italic = True

    # Section 7
    add_heading(doc, '7. Discussion: Locating TAB in Information Ontology and Logic Realism', 1)
    add_paragraph(doc, 'The transcendental derivation of the Bridge Identity establishes a prescriptive floor beneath contemporary information-based ontologies of physics. Much recent work proposes that physical reality is informational or mathematical in character. These frameworks often identify informational structure as fundamental but leave unresolved a central question: under what condition does informational possibility become concrete physical actuality?')

    add_heading(doc, '7.1 From "It from Bit" to Logical Actualization', 2)
    add_paragraph(doc, 'John Archibald Wheeler\'s "It from Bit" proposal suggested that physical reality arises from binary informational distinctions. Physical states correspond to answers to yes–no questions, and the structure of the universe reflects the accumulation of such informational choices.')
    add_paragraph(doc, 'Within TAB the distinction becomes explicit. Informational possibility is represented by the total informational domain I∞, the space of all structured distinctions. Physical actuality corresponds to the domain of configurations that obtain, A_Ω.')

    add_heading(doc, '7.2 Static Plenums and the Role of Primitive Action', 2)
    add_paragraph(doc, 'A different informational ontology appears in Max Tegmark\'s Mathematical Universe Hypothesis (MUH), which proposes that mathematical structure itself constitutes physical reality. Within this framework every consistent mathematical structure exists. Possibility and actuality collapse into a single category.')
    add_paragraph(doc, 'TAB preserves a distinction between these domains. Logical syntax and informational structure provide the formal vocabulary of possible configurations, but possibility does not entail actuality. A further primitive is required to mark which configurations obtain.')

    add_heading(doc, '7.7 Contrast with Modal Realism', 2)
    add_paragraph(doc, 'A natural question arises concerning the ontological status of non-actual configurations in I∞. If I∞ contains all L₃-admissible configurations, do the non-actualized ones "exist" in some robust sense?')
    add_paragraph(doc, 'TAB differs sharply from Lewisian modal realism, which treats non-actual possible worlds as concrete existents on par with our own. In TAB, non-actualized configurations in I∞ are structural possibilities, not concrete worlds. They are the configurations that L₃ permits and that A could mark as obtaining, but which lack the obtaining marker.')

    # Section 8
    add_heading(doc, '8. Consequences for Ontology', 1)

    add_heading(doc, '8.1 What the Equation Claims', 2)
    add_paragraph(doc, 'The bridge equation establishes that the structure of actuality is not arbitrary. Reality has a form: it is the logically admissible informational configurations of the total possibility space. This form is not imposed from outside but constituted by the interaction of the primitives.')

    add_heading(doc, '8.2 What the Equation Does Not Claim', 2)
    add_paragraph(doc, 'The bridge equation does not claim:')
    add_paragraph(doc, '• That we can derive specific physical laws from pure reason. Physics requires additional assumptions (empirical regularities, operational constraints) that are not contained in the primitive ontology.')
    add_paragraph(doc, '• That the primitives are causally prior to the physical world. The grounding relation is not temporal.')
    add_paragraph(doc, '• That the bridge equation is empirically testable in isolation. The equation is a framework, not a hypothesis.')

    # Section 9
    add_heading(doc, '9. Conclusion', 1)
    add_paragraph(doc, 'We have argued that three primitives—prescriptive logical constraint (L₃), total informational possibility (I∞), and actualization (A)—are each transcendentally necessary and jointly constitute the minimal ontology of reality. Their interaction yields the core physics bridge of Logic Realism Theory.')

    # Bridge Result box
    doc.add_paragraph('─' * 30).alignment = WD_ALIGN_PARAGRAPH.CENTER
    p = doc.add_paragraph()
    p.add_run('Bridge Result').bold = True
    p.alignment = WD_ALIGN_PARAGRAPH.CENTER
    eq = doc.add_paragraph('χ ≡ [L₃ : I∞ : A]')
    eq.alignment = WD_ALIGN_PARAGRAPH.CENTER
    eq = doc.add_paragraph('χ ⊢ A_Ω')
    eq.alignment = WD_ALIGN_PARAGRAPH.CENTER
    eq = doc.add_paragraph('A_Ω = L₃(I∞)')
    eq.alignment = WD_ALIGN_PARAGRAPH.CENTER
    doc.add_paragraph('─' * 30).alignment = WD_ALIGN_PARAGRAPH.CENTER

    add_paragraph(doc, 'Actuality coincides with the logically admissible informational configurations of the total possibility space.')

    add_heading(doc, '9.1 Outlook for Physics', 2)
    add_paragraph(doc, 'The bridge identity constrains candidate physical theories in at least one concrete way: any physical structure must be realizable within A_Ω = L₃(I∞). This rules out physical theories that require ontological contradictions (states that are both P and not-P), configurations that cannot be distinguished from others (violations of identity), or structures that presuppose a possibility space narrower than L₃ permits without explanatory justification.')

    # Appendix A
    add_heading(doc, 'Appendix A: Primitive Definitions', 1)
    add_table(doc,
              ['Symbol', 'Name', 'Definition'],
              [
                  ['L₃', 'Prescriptive logical constraint structure', 'The triadic constraint of identity, non-contradiction, and excluded middle, understood as governing what can obtain, not merely what can be thought.'],
                  ['I∞', 'Total informational possibility space', 'The complete domain of distinguishable configurations; exhausts the space of what might obtain.'],
                  ['A', 'Actualization primitive', 'The irreducible marking of configurations as obtaining; bridges possibility and actuality.'],
                  ['χ', 'Primitive ontology', 'The co-constitutive unity of L₃, I∞, and A: χ ≡ [L₃ : I∞ : A].'],
                  ['A_Ω', 'Actualized domain', 'The totality of what obtains; the result of A operating on I∞ under L₃.'],
                  ['L₃(I∞)', 'Logically admissible configurations', 'The subset of I∞ consisting of configurations that satisfy L₃.']
              ])

    # Appendix B
    add_heading(doc, 'Appendix B: Logical Notation', 1)
    add_table(doc,
              ['Symbol', 'Meaning'],
              [
                  ['≡', 'Definitional equivalence'],
                  ['⊢', 'Ontological grounding (read: "grounds" or "constitutes")'],
                  ['χ', 'Chi; the primitive ontological unity'],
                  ['=', 'Identity'],
                  ['[A : B : C]', 'Co-constitutive unity of A, B, and C'],
                  ['∞ (subscript)', 'Completeness; exhausting the domain'],
                  ['Ω (subscript)', 'Actualized; obtaining']
              ])

    # Appendix C
    add_heading(doc, 'Appendix C: Formalization Status', 1)
    add_paragraph(doc, 'The ontological framework presented in this paper has been partially formalized in Lean 4. The formalization project verifies the logical structure of the reconstruction chain that proceeds from the primitives established here. Current status (March 2026): 22 axioms, 0 unresolved proof obligations (sorries), representing a 50% reduction from the initial 44 axioms.')

    add_heading(doc, 'Axiom Classification', 2)
    add_table(doc,
              ['Category', 'Count', 'Description'],
              [
                  ['PRIMITIVE', '3', 'Ontological commitments (I, I_infinite, bridge_principle)'],
                  ['EXTERNAL', '19', 'Established mathematics (Gleason, Stone, Hardy, etc.)'],
                  ['REMAINING', '0', 'All derivable axioms converted to theorems']
              ])

    # References
    add_heading(doc, 'References', 1)
    refs = [
        'Chiribella, G., D\'Ariano, G. M., & Perinotti, P. (2011). Informational derivation of quantum theory. Physical Review A, 84(1), 012311.',
        'da Costa, N. C. A., & de Ronde, C. (2013). The paraconsistent logic of quantum superpositions. Foundations of Physics, 43(7), 845–858.',
        'Floridi, L. (2011). The Philosophy of Information. Oxford University Press.',
        'Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv preprint quant-ph/0101012.',
        'Priest, G. (2006). In Contradiction: A Study of the Transconsistent (2nd ed.). Oxford University Press.',
        'Tahko, T. E. (2014). The metaphysics of logic. In P. Rush (Ed.), The Metaphysics of Logic (pp. 1–17). Cambridge University Press.',
        'Tegmark, M. (2014). Our Mathematical Universe: My Quest for the Ultimate Nature of Reality. Knopf.',
        'Wheeler, J. A. (1990). Information, physics, quantum: The search for links. In W. H. Zurek (Ed.), Complexity, Entropy, and the Physics of Information (pp. 3–28). Addison-Wesley.'
    ]
    for ref in refs:
        add_paragraph(doc, ref)

    # Save
    output_path = DOCS_DIR / 'TAB-v2.0.docx'
    doc.save(str(output_path))
    print(f"Generated: {output_path}")
    return output_path

def generate_master_docx():
    """Generate LRT-MASTER-v2.0.docx with proper formatting."""
    doc = Document()

    # Set document defaults
    style = doc.styles['Normal']
    style.font.name = 'Times New Roman'
    style.font.size = Pt(12)

    # Title
    title = doc.add_heading('Logic Realism Theory: Quantum Reconstruction from Logical Constraint', 0)
    title.alignment = WD_ALIGN_PARAGRAPH.CENTER

    # Subtitle
    subtitle = doc.add_paragraph('Part II: Physics Reconstruction')
    subtitle.alignment = WD_ALIGN_PARAGRAPH.CENTER
    for run in subtitle.runs:
        run.italic = True
        run.font.size = Pt(14)

    # Author info
    doc.add_paragraph()
    info_table = [
        ['Author:', 'James D. Longmire'],
        ['Affiliation:', 'Northrop Grumman Fellow (unaffiliated research)'],
        ['ORCID:', '0009-0009-1383-7698'],
        ['Correspondence:', 'jdlongmire@outlook.com'],
        ['Date:', 'March 2026'],
        ['Version:', '2.0'],
        ['Status:', 'Pre-print'],
        ['Companion paper:', 'The Actualization Bridge (TAB, Part I)']
    ]
    for label, value in info_table:
        p = doc.add_paragraph()
        p.add_run(label).bold = True
        p.add_run(' ' + value)

    doc.add_paragraph('─' * 50).alignment = WD_ALIGN_PARAGRAPH.CENTER

    # Abstract
    add_heading(doc, 'Abstract', 1)
    abstract_text = """Assuming the result established in the companion paper TAB—that physical actuality is constituted by the primitive ontic state χ ≡ [L₃ : I∞ : A], where L₃ denotes the three fundamental laws of logic, I∞ the complete informational domain, and A the actualization operator—this paper derives the full structure of non-relativistic quantum mechanics. The derivation proceeds through ten steps: from the bridge equation A_Ω = L₃(I∞) through determinate identity, local tomography, complex Hilbert space, projection-valued measures, the Born rule, unitarity, temporal emergence, and the Schrödinger equation. Each step is marked by epistemic status (ESTABLISHED, ARGUED, or OPEN) and has been formalized in Lean 4 with 22 axioms and zero sorries. The reconstruction subsumes competing programs (Hardy, CDP, Masanes-Müller) while grounding their axioms rather than postulating them."""
    add_paragraph(doc, abstract_text)

    kw = doc.add_paragraph()
    kw.add_run('Keywords: ').bold = True
    kw.add_run('quantum reconstruction, logical realism, information ontology, Born rule, measurement problem, foundations of physics')

    doc.add_paragraph('─' * 50).alignment = WD_ALIGN_PARAGRAPH.CENTER

    # Section 1
    add_heading(doc, '1. Foundational Assumption', 1)

    add_heading(doc, '1.1 The TAB Result', 2)
    add_paragraph(doc, 'This paper assumes the result established in the companion paper The Actualization Bridge (TAB):')
    p = doc.add_paragraph()
    p.add_run('Physical actuality is constituted by the primitive ontic state χ ≡ [L₃ : I∞ : A], yielding the bridge equation A_Ω = L₃(I∞).').italic = True

    add_paragraph(doc, 'Three guiding observations motivate the primitives:')

    add_table(doc,
              ['Observation', 'Content', 'Primitive'],
              [
                  ['1', 'Physical reality exhibits logical structure: identity, non-contradiction, determinacy', 'L₃'],
                  ['2', 'Physical reality exhibits informational structure: distinguishable configurations, entropy', 'I∞'],
                  ['3', 'Physical reality is dynamic: actuality is not static but constituted', 'A']
              ])

    # Figure 1
    add_image_if_exists(doc, 'LRT-derivation-chain-v2.png',
                       'Figure 1: Complete derivation chain from χ to Schrödinger equation. Current Lean status: 22 axioms (3 primitive, 19 external), 0 sorries.')

    add_heading(doc, '1.2 The Physical Proposition Criterion', 2)
    add_paragraph(doc, 'TAB establishes that L₃\'s constitutive status entails operational distinguishability for all physical propositions:')
    p = doc.add_paragraph()
    p.add_run('Physical Proposition Criterion (PPC): ').bold = True
    p.add_run('A claim Q counts as a physical proposition if and only if Q satisfies L₃. Satisfying L₃ requires that Q-true and Q-false are operationally distinguishable.')

    add_heading(doc, '1.3 What This Paper Does', 2)
    add_paragraph(doc, 'Given the TAB result, this paper derives the structure of non-relativistic quantum mechanics:')
    items = ['Complex Hilbert space ℂH (Step 4)', 'Projection-valued measures (Step 5)', 'The Born rule (Step 6)',
             'Unitary dynamics (Step 7)', 'Continuous time (Step 8)', 'The Schrödinger equation (Step 10)']
    for item in items:
        add_paragraph(doc, '• ' + item)

    add_paragraph(doc, 'Each step is marked with epistemic status:')
    add_paragraph(doc, '• ESTABLISHED: Imported from peer-reviewed mathematics')
    add_paragraph(doc, '• ARGUED: Defended with explicit reasoning; LRT\'s original contribution')
    add_paragraph(doc, '• OPEN: Identified for future work')

    # Section 2
    add_heading(doc, '2. From χ to Quantum Structure', 1)

    add_heading(doc, '2.1 Determinate Identity', 2)
    p = doc.add_paragraph()
    p.add_run('Claim: ').bold = True
    p.add_run('Every actual configuration c ∈ A_Ω satisfies Determinate Identity. ')
    p.add_run('[ESTABLISHED]').italic = True

    add_paragraph(doc, 'This follows directly from A_Ω = L₃(I∞). Configurations in A_Ω are L₃-admissible by definition.')

    add_heading(doc, '2.2 Local Tomography', 2)
    p = doc.add_paragraph()
    p.add_run('Claim: ').bold = True
    p.add_run('Any theory describing actual configurations in A_Ω must satisfy local tomography. ')
    p.add_run('[ARGUED]').italic = True

    add_paragraph(doc, 'The argument proceeds in two stages:')
    p = doc.add_paragraph()
    p.add_run('H1 (Metaphysical Supervenience): ').bold = True
    p.add_run('Each subsystem has determinate identity. The composite is nothing over and above its subsystems relationally organized.')
    p = doc.add_paragraph()
    p.add_run('H2 (Operational Local Tomography): ').bold = True
    p.add_run('The composite state is completely determined by local measurement statistics.')

    add_heading(doc, '2.3 Complex Hilbert Space', 2)
    p = doc.add_paragraph()
    p.add_run('Claim: ').bold = True
    p.add_run('The state space is complex Hilbert space ℂH. ')
    p.add_run('[ESTABLISHED]').italic = True

    add_paragraph(doc, 'Theorem (Masanes and Müller, 2011): Among generalized probabilistic theories, local tomography + continuous reversible dynamics + entanglement existence + no restriction on observables uniquely select complex Hilbert space quantum mechanics.')

    # Figure: Dimension Scaling
    add_image_if_exists(doc, 'dimension-scaling.png',
                       'Figure 2: State space dimension scaling for different field parameters K. Only K=2 (complex) maintains manageable information scaling while supporting entanglement.')

    add_heading(doc, '2.4 Projection-Valued Measures', 2)
    p = doc.add_paragraph()
    p.add_run('Claim: ').bold = True
    p.add_run('Event operators on ℂH representing actualization predicates are projections. ')
    p.add_run('[ARGUED]').italic = True

    add_paragraph(doc, 'The actualization primitive A is Boolean: A : D → {0, 1}. For any configuration c and event E, A(E, c) ∈ {0, 1}. There is no intermediate actualization.')

    add_heading(doc, '2.5 The Born Rule', 2)
    p = doc.add_paragraph()
    p.add_run('Claim: ').bold = True
    p.add_run('The unique probability measure on PVM structure is the Born rule. ')
    p.add_run('[ESTABLISHED]').italic = True

    add_paragraph(doc, 'Theorem (Gleason, 1957): For dim(H) ≥ 3, any frame function on closed subspaces has the form μ(P) = Tr(ρP) for a unique density operator ρ.')

    # Figure: Born Rule
    add_image_if_exists(doc, 'born-rule-simplex.png',
                       'Figure 3: Born rule emergence from Gleason constraints.')

    add_heading(doc, '2.6 Unitarity', 2)
    p = doc.add_paragraph()
    p.add_run('Claim: ').bold = True
    p.add_run('Time evolution is unitary. ')
    p.add_run('[ESTABLISHED]').italic = True

    add_heading(doc, '2.7 Temporal Structure', 2)
    p = doc.add_paragraph()
    p.add_run('Claim: ').bold = True
    p.add_run('Ordinal time emerges from A\'s Boolean character; continuous time from trajectory topology. ')
    p.add_run('[ARGUED]').italic = True

    p = doc.add_paragraph()
    p.add_run('Unique Next State (UNS): ').bold = True
    p.add_run('For every c ∈ A_Ω, there exists a unique successor c\' that A selects.')

    add_heading(doc, '2.8 The Schrödinger Equation', 2)
    p = doc.add_paragraph()
    p.add_run('Claim: ').bold = True
    p.add_run('The equation of motion is the Schrödinger equation. ')
    p.add_run('[ESTABLISHED]').italic = True

    add_paragraph(doc, 'Theorem (Stone, 1930): A strongly continuous one-parameter unitary group U(t) has a unique self-adjoint generator H with U(t) = exp(−iHt/ℏ).')
    add_paragraph(doc, 'Differentiation yields: iℏ d/dt|ψ(t)⟩ = H|ψ(t)⟩')

    add_heading(doc, '2.9 Summary of Derivation Chain', 2)
    add_table(doc,
              ['Step', 'Content', 'Status', 'Lean'],
              [
                  ['0', 'Primitives: χ ≡ [L₃ : I∞ : A]', 'ASSUMED (TAB)', '✓'],
                  ['1', 'Bridge: A_Ω = L₃(I∞)', 'ASSUMED (TAB)', '✓'],
                  ['2', 'Determinate Identity', 'ESTABLISHED', '✓'],
                  ['3', 'Local Tomography', 'ARGUED', '✓'],
                  ['4', 'Complex Hilbert Space', 'ESTABLISHED', '✓'],
                  ['5', 'PVM Structure', 'ARGUED', '✓'],
                  ['6', 'Born Rule', 'ESTABLISHED', '✓'],
                  ['7', 'Unitarity', 'ESTABLISHED', '✓'],
                  ['8', 'Temporal Emergence', 'ARGUED', '✓'],
                  ['9', 'Energy-Action', 'ESTABLISHED', '✓'],
                  ['10', 'Schrödinger Equation', 'ESTABLISHED', '✓']
              ])

    add_paragraph(doc, 'Axiom count: 22 (3 primitive + 19 external/imported + 0 derivation targets remaining)')

    # Section 3
    add_heading(doc, '3. Resolution of Standing Problems', 1)
    add_paragraph(doc, 'The standing problems of quantum foundations dissolve under LRT. Each arises from a presupposition LRT does not share.')

    problems = [
        ('3.1 The Measurement Problem', 'Unitary evolution is linear; measurement yields one definite outcome. What produces the transition?',
         'A is the primitive dynamic aspect of χ, not a process within A_Ω. There is no collapse because nothing collapses—the superposition |ψ⟩ is the state in ℂH; A selects one Boolean outcome from its PVM decomposition.'),
        ('3.2 Wave-Particle Duality', 'Quantum systems exhibit wave behavior (interference) and particle behavior (definite outcomes). What are they?',
         'The wave aspect is the configuration in I∞; the particle aspect is what A selects into A_Ω. These are not competing descriptions but descriptions at two levels: possibility space (I∞) and actuality (A_Ω).'),
        ('3.3 EPR and Nonlocality', 'Entangled systems exhibit correlations violating Bell inequalities. No local hidden variables can reproduce them.',
         'Entangled states are non-decomposable configurations in I∞—their identity cannot be factored into subsystem identities. A_Ω is global; A evaluates joint configurations, not local subsystems independently.'),
        ('3.4 Schrödinger\'s Cat', 'Macroscopic superpositions seem to exist before observation.',
         'The superposition |alive⟩ + |dead⟩ exists in I∞—it is representable and evolves unitarily. It is not in A_Ω as a superposition. A selects one L₃-admissible outcome.')
    ]

    for title, problem, dissolution in problems:
        add_heading(doc, title, 2)
        p = doc.add_paragraph()
        p.add_run('Problem: ').bold = True
        p.add_run(problem)
        p = doc.add_paragraph()
        p.add_run('Dissolution: ').bold = True
        p.add_run(dissolution)

    # Section 4
    add_heading(doc, '4. Discussion', 1)

    add_heading(doc, '4.1 Comparison to Reconstruction Programs', 2)
    add_table(doc,
              ['Framework', 'Starting Point', 'What\'s Unexplained'],
              [
                  ['Hardy (2001)', '5 operational axioms', 'Why these axioms?'],
                  ['CDP (2011)', '6 informational principles', 'Why information is primitive?'],
                  ['Masanes-Müller (2011)', '5 physical requirements', 'Why these requirements?'],
                  ['LRT', 'χ = [L₃ : I∞ : A]', 'Grounds the above']
              ])

    add_paragraph(doc, 'The subsumption claim: LRT does not compete with these programs—it subsumes them. Hardy\'s axioms become derivable given χ. CDP\'s purification principle follows from Boolean actualization. Masanes-Müller\'s requirements are consequences of I∞ structure.')

    add_heading(doc, '4.2 What LRT Derives vs. Assumes', 2)
    add_table(doc,
              ['Feature', 'Competitor Status', 'LRT Status'],
              [
                  ['Local tomography', 'Axiom', 'Derived (H1/H2 bridge)'],
                  ['Boolean measurement', 'Assumed', 'Derived (A binary)'],
                  ['PVM structure', 'Assumed', 'Derived (eigenvalue restriction)'],
                  ['Born rule', 'Derived or assumed', 'Derived (Gleason on derived PVM)'],
                  ['Temporal structure', 'Assumed', 'Derived (UNS + Debreu-Nachbin)']
              ])

    add_heading(doc, '4.3 Explanatory Power Inventory', 2)
    add_table(doc,
              ['Phenomenon', 'Standard Status', 'LRT Status'],
              [
                  ['Born rule', 'Postulated / derived', 'Derived (Gleason + Boolean A)'],
                  ['Measurement problem', 'Interpretation-dependent', 'Dissolved (A constitutes)'],
                  ['Superposition', 'Ontologically ambiguous', 'Incomplete specification in I∞'],
                  ['Entanglement', 'Nonlocal correlations', 'Global L₃ constraint'],
                  ['Local tomography', 'Axiom', 'Derived (H1/H2)'],
                  ['K=2 (complex field)', 'Axiom', 'Derived (multiple routes)'],
                  ['EPR paradox', 'Interpretation-dependent', 'Dissolved (A is global)']
              ])

    add_heading(doc, '4.4 Falsification and Null Hypothesis', 2)
    p = doc.add_paragraph()
    p.add_run('Null hypothesis (H₀): ').bold = True
    p.add_run('Operational constraints suffice without ontological grounding. QM\'s axioms are "just the way things are."')
    p = doc.add_paragraph()
    p.add_run('LRT\'s claim against H₀: ').bold = True
    p.add_run('The axioms are not arbitrary—they follow from χ. LRT adds explanatory value by answering "why these axioms?"')

    add_table(doc,
              ['Level', 'Falsifier', 'Severity'],
              [
                  ['Categorical', 'L₃ violation in completed physical record', 'Fatal to hard core'],
                  ['Structural', 'Super-quantum correlations, primitive POVMs', 'Revision of argued steps'],
                  ['Empirical', 'Real QM confirmed over complex (Renou et al.)', 'Test downstream predictions']
              ])

    # Section 5
    add_heading(doc, '5. Open Problems', 1)

    add_heading(doc, '5.1 Current Formalization Status', 2)
    add_table(doc,
              ['Metric', 'Value'],
              [
                  ['Build', 'SUCCESS (2491 jobs)'],
                  ['Axioms', '22'],
                  ['Sorries', '0'],
                  ['PRIMITIVE', '3 (I, I_infinite, bridge_principle)'],
                  ['EXTERNAL', '19 (Gleason, Stone, Hardy, CDP, etc.)'],
                  ['REMAINING', '0 (all derivation targets eliminated)']
              ])

    # Figure: Axiom Timeline
    add_image_if_exists(doc, 'axiom-timeline.png',
                       'Figure 4: Axiom reduction journey from December 2025 to March 2026. Initial count: 44 axioms with 12 sorries. Current: 22 axioms with 0 sorries (50% reduction).')

    add_heading(doc, '5.2 Derivation Targets (COMPLETE)', 2)
    add_paragraph(doc, 'All REMAINING axioms have been converted to theorems as of March 2026:')
    add_table(doc,
              ['Group', 'Former Axioms', 'Current Status'],
              [
                  ['Step 5', 'spectral_correspondence', 'THEOREM (Issue #38)'],
                  ['Step 6', 'proj_norm_le, born_rule_completeness', 'THEOREMS (Cauchy-Schwarz, Parseval)'],
                  ['Step 7', 'Evolution family (4 axioms)', 'DEFINITIONS/THEOREMS (Hamiltonian approach)'],
                  ['Step 8', 'Temporal embedding (3 axioms)', 'DEFINITIONS/THEOREMS (ℕ-indexed)']
              ])

    add_paragraph(doc, 'Final result: 44 → 22 axioms (50% reduction achieved).')

    add_heading(doc, '5.3 Extensions', 2)
    add_table(doc,
              ['Problem', 'Type', 'Priority'],
              [
                  ['Relativistic extension', 'Extension', 'Medium'],
                  ['Quantum field theory', 'Extension', 'Long-range'],
                  ['Fine-structure constant', 'Extension', 'Speculative'],
                  ['Cosmological application', 'Extension', 'Open'],
                  ['Bekenstein-Hawking connection', 'Gap', 'High']
              ])

    # Section 6
    add_heading(doc, '6. Conclusion', 1)
    add_paragraph(doc, 'Assuming the TAB result—that physical actuality is constituted by χ ≡ [L₃ : I∞ : A], yielding A_Ω = L₃(I∞)—this paper has derived the complete structure of non-relativistic quantum mechanics. The derivation is formalized in Lean 4 with 22 axioms (3 primitive, 19 imported, 0 open targets) and zero sorries.')
    add_paragraph(doc, 'LRT\'s contribution is precisely located: not new mathematics, but a new grounding argument for existing mathematics. The reconstruction programs of Hardy, CDP, and Masanes-Müller are subsumed—their axioms become consequences of χ rather than postulates. Standing problems dissolve: measurement, EPR, wave-particle duality, Schrödinger\'s cat, preferred basis, the observer. Each arises from a presupposition LRT does not share.')
    add_paragraph(doc, 'The null hypothesis—that operational constraints suffice without grounding—is rejected. LRT answers the question reconstruction programs leave open: why these axioms?')

    # Appendix A
    add_heading(doc, 'Appendix A: QM Primitives to LRT Origins', 1)
    add_table(doc,
              ['QM Primitive', 'Standard Status', 'LRT Origin', 'Step'],
              [
                  ['Hilbert space ℂH', 'Postulated', 'Masanes-Müller', '4'],
                  ['Complex field', 'Postulated', 'Local tomography', '4'],
                  ['Pure states', 'Postulated', 'ℂH structure', '4'],
                  ['Observables', 'Postulated', 'PVM + spectral theorem', '5'],
                  ['Born rule', 'Postulated', 'Gleason on PVM', '6'],
                  ['Tensor products', 'Postulated', 'Local tomography', '4'],
                  ['Unitary evolution', 'Postulated', 'G-equivariance + Stone', '7-9'],
                  ['Schrödinger equation', 'Postulated', 'Stone on U(t)', '10'],
                  ['Definite outcomes', 'Postulated', 'A primitive', '2']
              ])

    # Appendix B
    add_heading(doc, 'Appendix B: Axiom Classification', 1)
    p = doc.add_paragraph()
    p.add_run('PRIMITIVE (3): ').bold = True
    p.add_run('Irreducible LRT commitments — I : Type*, I_infinite, bridge_principle')
    p = doc.add_paragraph()
    p.add_run('EXTERNAL (19): ').bold = True
    p.add_run('Established mathematics, axiomatized for Lean efficiency — Hardy reconstruction (2), Quantum state space (2), Purification/CDP (2), Born rule/Gleason (4), Unitarity/Hamiltonian (2), Functional analysis (5), Physical constants (2)')
    p = doc.add_paragraph()
    p.add_run('REMAINING (0): ').bold = True
    p.add_run('All derivation targets eliminated — 50% reduction from initial 44 axioms')

    # Figure: Axiom Treemap
    add_image_if_exists(doc, 'axiom-treemap.png',
                       'Figure 5: Visual breakdown of 22 axioms by classification.')

    # References
    add_heading(doc, 'References', 1)
    refs = [
        'Busch, P. (2003). Quantum states and generalized observables: A simple proof of Gleason\'s theorem. Physical Review Letters, 91(12), 120403.',
        'Chiribella, G., D\'Ariano, G. M., and Perinotti, P. (2011). Informational derivation of quantum theory. Physical Review A, 84(1), 012311.',
        'Debreu, G. (1954). Representation of a preference ordering by a numerical function. In R. M. Thrall et al. (Eds.), Decision Processes (pp. 159-165). Wiley.',
        'Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. Journal of Mathematics and Mechanics, 6(6), 885-893.',
        'Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012.',
        'Masanes, L. and Müller, M. P. (2011). A derivation of quantum theory from physical requirements. New Journal of Physics, 13(6), 063001.',
        'Renou, M.-O., et al. (2021). Quantum theory based on real numbers can be experimentally falsified. Nature, 600, 625-629.',
        'Stone, M. H. (1930). Linear transformations in Hilbert space III. PNAS, 16(2), 172-175.'
    ]
    for ref in refs:
        add_paragraph(doc, ref)

    # Save
    output_path = DOCS_DIR / 'LRT-MASTER-v2.0.docx'
    doc.save(str(output_path))
    print(f"Generated: {output_path}")
    return output_path


if __name__ == '__main__':
    print("Generating TAB-v2.0.docx...")
    generate_tab_docx()
    print()
    print("Generating LRT-MASTER-v2.0.docx...")
    generate_master_docx()
    print()
    print("Done!")
