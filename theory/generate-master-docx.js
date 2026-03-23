const { Document, Packer, Paragraph, TextRun, Table, TableRow, TableCell, ImageRun,
        Header, Footer, AlignmentType, PageOrientation, LevelFormat, ExternalHyperlink,
        HeadingLevel, BorderStyle, WidthType, ShadingType, PageNumber, PageBreak,
        TableOfContents } = require('docx');
const fs = require('fs');
const path = require('path');

const figuresDir = path.join(__dirname, 'figures');

// Helper to load image
function loadImage(filename) {
  const filepath = path.join(figuresDir, filename);
  if (fs.existsSync(filepath)) {
    return fs.readFileSync(filepath);
  }
  console.warn(`Image not found: ${filepath}`);
  return null;
}

// Helper to create image paragraph
function createImage(filename, width, height, caption, figNum) {
  const data = loadImage(filename);
  if (!data) return [new Paragraph({ children: [new TextRun({ text: `[Image not found: ${filename}]`, italics: true })] })];

  const children = [
    new Paragraph({
      alignment: AlignmentType.CENTER,
      spacing: { before: 240, after: 120 },
      children: [new ImageRun({
        type: 'png',
        data: data,
        transformation: { width, height },
        altText: { title: caption, description: caption, name: filename }
      })]
    }),
    new Paragraph({
      alignment: AlignmentType.CENTER,
      spacing: { after: 240 },
      children: [
        new TextRun({ text: `Figure ${figNum}: `, italics: true, bold: true }),
        new TextRun({ text: caption, italics: true })
      ]
    })
  ];
  return children;
}

// Helper for section heading
function h1(text) {
  return new Paragraph({
    heading: HeadingLevel.HEADING_1,
    spacing: { before: 400, after: 200 },
    children: [new TextRun({ text, bold: true, size: 32 })]
  });
}

function h2(text) {
  return new Paragraph({
    heading: HeadingLevel.HEADING_2,
    spacing: { before: 300, after: 150 },
    children: [new TextRun({ text, bold: true, size: 28 })]
  });
}

function h3(text) {
  return new Paragraph({
    heading: HeadingLevel.HEADING_3,
    spacing: { before: 240, after: 120 },
    children: [new TextRun({ text, bold: true, size: 26 })]
  });
}

function para(text, options = {}) {
  const runs = [];
  // Simple parser for **bold** and *italic*
  const parts = text.split(/(\*\*[^*]+\*\*|\*[^*]+\*)/g);
  for (const part of parts) {
    if (part.startsWith('**') && part.endsWith('**')) {
      runs.push(new TextRun({ text: part.slice(2, -2), bold: true }));
    } else if (part.startsWith('*') && part.endsWith('*')) {
      runs.push(new TextRun({ text: part.slice(1, -1), italics: true }));
    } else {
      runs.push(new TextRun({ text: part }));
    }
  }
  return new Paragraph({
    spacing: { after: 200 },
    alignment: options.center ? AlignmentType.CENTER : AlignmentType.LEFT,
    children: runs
  });
}

function blockquote(text) {
  return new Paragraph({
    spacing: { after: 200 },
    indent: { left: 720, right: 720 },
    children: [new TextRun({ text, italics: true })]
  });
}

function equation(text) {
  return new Paragraph({
    alignment: AlignmentType.CENTER,
    spacing: { before: 120, after: 120 },
    children: [new TextRun({ text, italics: true })]
  });
}

// Table helper
const border = { style: BorderStyle.SINGLE, size: 1, color: "CCCCCC" };
const borders = { top: border, bottom: border, left: border, right: border };

function createTable(headers, rows, colWidths) {
  const tableWidth = colWidths.reduce((a, b) => a + b, 0);

  const headerRow = new TableRow({
    children: headers.map((h, i) => new TableCell({
      borders,
      width: { size: colWidths[i], type: WidthType.DXA },
      shading: { fill: "E8E8E8", type: ShadingType.CLEAR },
      margins: { top: 80, bottom: 80, left: 120, right: 120 },
      children: [new Paragraph({ children: [new TextRun({ text: h, bold: true })] })]
    }))
  });

  const dataRows = rows.map(row => new TableRow({
    children: row.map((cell, i) => new TableCell({
      borders,
      width: { size: colWidths[i], type: WidthType.DXA },
      margins: { top: 80, bottom: 80, left: 120, right: 120 },
      children: [new Paragraph({ children: [new TextRun({ text: cell })] })]
    }))
  }));

  return new Table({
    width: { size: tableWidth, type: WidthType.DXA },
    columnWidths: colWidths,
    rows: [headerRow, ...dataRows]
  });
}

// Build document
const doc = new Document({
  styles: {
    default: {
      document: {
        run: { font: "Times New Roman", size: 24 }
      }
    },
    paragraphStyles: [
      { id: "Heading1", name: "Heading 1", basedOn: "Normal", next: "Normal", quickFormat: true,
        run: { size: 32, bold: true, font: "Arial" },
        paragraph: { spacing: { before: 400, after: 200 }, outlineLevel: 0 } },
      { id: "Heading2", name: "Heading 2", basedOn: "Normal", next: "Normal", quickFormat: true,
        run: { size: 28, bold: true, font: "Arial" },
        paragraph: { spacing: { before: 300, after: 150 }, outlineLevel: 1 } },
      { id: "Heading3", name: "Heading 3", basedOn: "Normal", next: "Normal", quickFormat: true,
        run: { size: 26, bold: true, font: "Arial" },
        paragraph: { spacing: { before: 240, after: 120 }, outlineLevel: 2 } },
    ]
  },
  sections: [{
    properties: {
      page: {
        size: { width: 12240, height: 15840 },
        margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 }
      }
    },
    headers: {
      default: new Header({
        children: [new Paragraph({
          children: [new TextRun({ text: "Logic Realism Theory: Quantum Reconstruction", italics: true, size: 20 })]
        })]
      })
    },
    footers: {
      default: new Footer({
        children: [new Paragraph({
          alignment: AlignmentType.CENTER,
          children: [new TextRun({ text: "Page " }), new TextRun({ children: [PageNumber.CURRENT] })]
        })]
      })
    },
    children: [
      // Title
      new Paragraph({
        alignment: AlignmentType.CENTER,
        spacing: { after: 200 },
        children: [new TextRun({ text: "Logic Realism Theory:", bold: true, size: 40 })]
      }),
      new Paragraph({
        alignment: AlignmentType.CENTER,
        spacing: { after: 400 },
        children: [new TextRun({ text: "Quantum Reconstruction from Logical Constraint", bold: true, size: 36 })]
      }),

      // Author info
      para("**Author:** James D. Longmire", { center: true }),
      para("**Affiliation:** Northrop Grumman Fellow (unaffiliated research)", { center: true }),
      para("**ORCID:** 0009-0009-1383-7698", { center: true }),
      para("**Correspondence:** jdlongmire@outlook.com", { center: true }),
      para("**Date:** March 2026", { center: true }),
      para("**Version:** 2.0", { center: true }),
      para("**Status:** Pre-print", { center: true }),
      para("**Companion paper:** *The Actualized Bridge: Transcendental Constitution of Physical Reality* (TAB)", { center: true }),

      new Paragraph({ children: [new PageBreak()] }),

      // Abstract
      h1("Abstract"),
      para("Assuming the result established in the companion paper TAB\u2014that physical actuality is constituted by the primitive ontic state \u03C7 \u2261 [L\u2083 : I\u221E : A], where L\u2083 denotes the three fundamental laws of logic, I\u221E the complete informational domain, and A the actualization operator\u2014this paper derives the full structure of non-relativistic quantum mechanics. The derivation proceeds through ten steps: from the bridge equation A_\u03A9 = L\u2083(I\u221E) through determinate identity, local tomography, complex Hilbert space, projection-valued measures, the Born rule, unitarity, temporal emergence, and the Schr\u00F6dinger equation. Each step is marked by epistemic status (ESTABLISHED, ARGUED, or OPEN) and has been formalized in Lean 4 with 22 axioms (3 primitive, 19 external) and zero sorries. The reconstruction subsumes competing programs (Hardy, CDP, Masanes-M\u00FCller) while grounding their axioms rather than postulating them. Standing problems in quantum foundations\u2014measurement, EPR, wave-particle duality, Schr\u00F6dinger's cat\u2014dissolve rather than require solution. The theory satisfies Popperian falsifiability (categorical: L\u2083 violation in physical record) and Lakatosian progressiveness (structural selection of complex field confirmed by Renou et al. 2021). The null hypothesis is that operational constraints suffice without ontological grounding; LRT claims they do not."),

      para("**Keywords:** quantum reconstruction, logical realism, information ontology, Born rule, measurement problem, foundations of physics"),

      new Paragraph({ children: [new PageBreak()] }),

      // Table of Contents
      new TableOfContents("Table of Contents", { hyperlink: true, headingStyleRange: "1-3" }),

      new Paragraph({ children: [new PageBreak()] }),

      // Section 1
      h1("1. Foundational Assumption"),

      h2("1.1 The TAB Result"),
      para("This paper assumes the result established in the companion paper *The Actualized Bridge* (TAB):"),
      blockquote("Physical actuality is constituted by the primitive ontic state \u03C7 \u2261 [L\u2083 : I\u221E : A], yielding the bridge equation A_\u03A9 = L\u2083(I\u221E)."),
      para("The argument for this result is developed fully in TAB and summarized here only to fix notation. Three guiding observations motivate the primitives:"),

      createTable(
        ["Observation", "Content", "Primitive"],
        [
          ["1", "Physical reality exhibits logical structure: identity, non-contradiction, determinacy", "L\u2083"],
          ["2", "Physical reality exhibits informational structure: distinguishable configurations, entropy", "I\u221E"],
          ["3", "Physical reality is dynamic: actuality is not static but constituted", "A"]
        ],
        [1500, 5500, 1500]
      ),

      new Paragraph({ spacing: { after: 200 }, children: [] }),

      para("These three aspects are co-constitutive:"),
      equation("\u03C7 \u2261 [L\u2083 : I\u221E : A]"),
      para("The colon notation marks mutual constitution, not conjunction. Each aspect requires the others: L\u2083 without I\u221E has nothing to constrain; I\u221E without L\u2083 has no admissibility structure; both without A produce no actuality."),
      para("From \u03C7, TAB derives:"),
      equation("\u03C7 \u22A2 A_\u03A9 = L\u2083(I\u221E)"),
      para("where A_\u03A9 is the actualized domain\u2014the set of L\u2083-admissible configurations that A instantiates. This is the starting point for physics."),

      ...createImage("LRT-derivation-chain-v2.png", 550, 620, "Complete derivation chain from \u03C7 to Schr\u00F6dinger equation. Blue: primitives. Amber: bridge equation. Green: reconstruction steps. Purple: final results. External imports shown left; resolved phenomena shown right. Current Lean status: 22 axioms, 0 sorries.", 1),

      h2("1.2 The Physical Proposition Criterion"),
      para("TAB establishes that L\u2083's constitutive status entails operational distinguishability for all physical propositions:"),
      blockquote("Physical Proposition Criterion (PPC): A claim Q counts as a physical proposition if and only if Q satisfies L\u2083. Satisfying L\u2083 requires that Q-true and Q-false are operationally distinguishable. Any claim lacking this operational signature is not a physical proposition."),
      para("The PPC is not operationalism by stipulation. It follows from taking L\u2083 seriously as a constitutive condition on physical facts rather than as a filter on pre-formed propositions."),

      h2("1.3 What This Paper Does"),
      para("Given the TAB result, this paper derives the structure of non-relativistic quantum mechanics:"),
      para("\u2022 Complex Hilbert space \u2102H (Step 4)"),
      para("\u2022 Projection-valued measures (Step 5)"),
      para("\u2022 The Born rule (Step 6)"),
      para("\u2022 Unitary dynamics (Step 7)"),
      para("\u2022 Continuous time (Step 8)"),
      para("\u2022 The Schr\u00F6dinger equation (Step 10)"),
      para("Each step is marked with epistemic status:"),
      para("\u2022 **ESTABLISHED:** Imported from peer-reviewed mathematics"),
      para("\u2022 **ARGUED:** Defended with explicit reasoning; LRT's original contribution"),
      para("\u2022 **OPEN:** Identified for future work"),
      para("The derivation has been formalized in Lean 4. Current status: 22 axioms, 0 sorries (March 2026)."),

      new Paragraph({ children: [new PageBreak()] }),

      // Section 2
      h1("2. From \u03C7 to Quantum Structure"),

      h2("2.1 Determinate Identity"),
      para("**Claim:** Every actual configuration c \u2208 A_\u03A9 satisfies Determinate Identity. *[ESTABLISHED]*"),
      para("**Definition:** A configuration c \u2208 A_\u03A9 has Determinate Identity if and only if:"),
      equation("c = c  (Identity)"),
      equation("\u00AC(P(c) \u2227 \u00ACP(c))  for any property P  (Non-Contradiction)"),
      equation("P(c) \u2228 \u00ACP(c)  for any well-defined property P  (Excluded Middle)"),
      para("This follows directly from A_\u03A9 = L\u2083(I\u221E). Configurations in A_\u03A9 are L\u2083-admissible by definition."),

      h2("2.2 Local Tomography"),
      para("**Claim:** Any theory describing actual configurations in A_\u03A9 must satisfy local tomography. *[ARGUED]*"),
      para("**Definition:** A theory is *locally tomographic* if the state of a composite system is completely determined by the statistics of local measurements on its subsystems."),
      para("The argument proceeds in two stages:"),
      para("**H1 (Metaphysical Supervenience):** Each subsystem has determinate identity. The composite is nothing over and above its subsystems relationally organized. *[ESTABLISHED\u2014direct consequence of Determinate Identity]*"),
      para("**H2 (Operational Local Tomography):** The composite state is completely determined by local measurement statistics. *[ARGUED\u2014follows from H1 + PPC]*"),
      para("**The H1\u2192H2 argument:** For any relation R between subsystems to be a genuine physical relation, R must satisfy L\u2083. This requires operational distinguishability (PPC). Therefore every relation in H1's supervenience base is operationally accessible. Local tomography follows."),

      h2("2.3 Complex Hilbert Space"),
      para("**Claim:** The state space is complex Hilbert space \u2102H. *[ESTABLISHED]*"),
      para("**Theorem (Masanes and M\u00FCller, 2011):** Among generalized probabilistic theories, local tomography + continuous reversible dynamics + entanglement existence + no restriction on observables uniquely select complex Hilbert space quantum mechanics."),
      para("Local tomography is derived at Step 3. The remaining axioms are physical inputs characterizing the domain. Given these inputs, the state space is \u2102H. The field is complex, not real (Renou et al. 2021 confirms experimentally)."),

      ...createImage("dimension-scaling.png", 500, 350, "State space dimension scaling for different field parameters K. Only K=2 (complex) maintains manageable information scaling while supporting entanglement. K=1 (real) lacks interference; K\u22653 grows too rapidly for physical tractability.", 5),

      h2("2.4 Projection-Valued Measures"),
      para("**Claim:** Event operators on \u2102H representing actualization predicates are projections. *[ARGUED]*"),
      para("The actualization primitive A is Boolean:"),
      equation("A : D \u2192 {0, 1}"),
      para("For any configuration c and event E, A(E, c) \u2208 {0, 1}. There is no intermediate actualization."),
      para("**The eigenvalue restriction:**"),
      para("1. A's Boolean character entails Boolean actualization values"),
      para("2. Measurement outcomes are eigenvalues (spectral theorem)"),
      para("3. Therefore eigenvalues \u2208 {0, 1}"),
      para("4. Bounded self-adjoint operators with spectrum \u2286 {0, 1} satisfy P\u00B2 = P"),
      para("Event operators are projections. Collections form projection-valued measures (PVMs)."),

      h2("2.5 The Born Rule"),
      para("**Claim:** The unique probability measure on PVM structure is the Born rule. *[ESTABLISHED]*"),
      para("**Theorem (Gleason, 1957):** For dim(H) \u2265 3, any frame function on closed subspaces has the form \u03BC(P) = Tr(\u03C1P) for a unique density operator \u03C1."),
      para("The PVM structure from Step 5 provides the frame function conditions. Gleason's theorem delivers:"),
      equation("p(E|\u03C8) = \u27E8\u03C8|P_E|\u03C8\u27E9"),
      para("The Born rule is not postulated. It is the unique consistent probability measure the PVM structure admits."),

      ...createImage("born-rule-simplex.png", 500, 350, "Born rule emergence from Gleason constraints. Left: probability simplex showing valid probability distributions. Right: Bloch sphere representation of qubit states. Gleason's theorem forces the unique probability measure on the derived PVM structure.", 7),

      h2("2.6 Unitarity"),
      para("**Claim:** Time evolution is unitary. *[ESTABLISHED]*"),
      para("Determinate Identity at the sequence level requires that transitions preserve structural determinacy. Combined with norm preservation (Born rule consistency) and the symmetry group of A_\u03A9, this forces:"),
      para("\u2022 Time evolution operators U(t) form a strongly continuous one-parameter group"),
      para("\u2022 U(t) preserves inner products (unitarity)"),
      para("This is Wigner's theorem applied to the LRT context."),

      h2("2.7 Temporal Structure"),
      para("**Claim:** Ordinal time emerges from A's Boolean character; continuous time from trajectory topology. *[ARGUED]*"),
      para("**Unique Next State (UNS):** For every c \u2208 A_\u03A9, there exists a unique successor c' that A selects. This follows from Determinate Identity + Boolean A: Excluded Middle rules out indeterminate succession; Non-Contradiction rules out multiple successors."),
      para("UNS induces ordinal time. The Debreu-Nachbin theorem lifts ordinal structure to continuous \u211D-parameterization, given the Fubini-Study topology on state space."),

      h2("2.8 The Schr\u00F6dinger Equation"),
      para("**Claim:** The equation of motion is the Schr\u00F6dinger equation. *[ESTABLISHED]*"),
      para("**Theorem (Stone, 1930):** A strongly continuous one-parameter unitary group U(t) has a unique self-adjoint generator H with U(t) = exp(\u2212iHt/\u210F)."),
      para("Differentiation yields:"),
      equation("i\u210F (d/dt)|\u03C8(t)\u27E9 = H|\u03C8(t)\u27E9"),
      para("The Schr\u00F6dinger equation is derived, not postulated. Specific Hamiltonians remain empirical inputs."),

      h2("2.9 Summary of Derivation Chain"),
      createTable(
        ["Step", "Content", "Status", "Lean"],
        [
          ["0", "Primitives: \u03C7 \u2261 [L\u2083 : I\u221E : A]", "ASSUMED (TAB)", "\u2713"],
          ["1", "Bridge: A_\u03A9 = L\u2083(I\u221E)", "ASSUMED (TAB)", "\u2713"],
          ["2", "Determinate Identity", "ESTABLISHED", "\u2713"],
          ["3", "Local Tomography", "ARGUED", "\u2713"],
          ["4", "Complex Hilbert Space", "ESTABLISHED", "\u2713"],
          ["5", "PVM Structure", "ARGUED", "\u2713"],
          ["6", "Born Rule", "ESTABLISHED", "\u2713"],
          ["7", "Unitarity", "ESTABLISHED", "\u2713"],
          ["8", "Temporal Emergence", "ARGUED", "\u2713"],
          ["9", "Energy-Action", "ESTABLISHED", "\u2713"],
          ["10", "Schr\u00F6dinger Equation", "ESTABLISHED", "\u2713"]
        ],
        [1000, 4500, 2500, 800]
      ),
      new Paragraph({ spacing: { after: 200 }, children: [] }),
      para("**Axiom count:** 22 (3 primitive + 19 external/imported + 0 derivation targets)"),

      new Paragraph({ children: [new PageBreak()] }),

      // Section 3
      h1("3. Resolution of Standing Problems"),
      para("The standing problems of quantum foundations dissolve under LRT. Each arises from a presupposition LRT does not share."),

      h2("3.1 The Measurement Problem"),
      para("**Problem:** Unitary evolution is linear; measurement yields one definite outcome. What produces the transition?"),
      para("**Presupposition:** Measurement outcomes require dynamical explanation."),
      para("**Dissolution:** A is the primitive dynamic aspect of \u03C7, not a process within A_\u03A9. There is no collapse because nothing collapses\u2014the superposition |\u03C8\u27E9 is the state in \u2102H; A selects one Boolean outcome from its PVM decomposition. The measurement problem does not arise because LRT does not treat measurement as requiring a dynamical account."),

      h2("3.2 Wave-Particle Duality"),
      para("**Problem:** Quantum systems exhibit wave behavior (interference) and particle behavior (definite outcomes). What are they?"),
      para("**Presupposition:** A system must be one kind of thing."),
      para("**Dissolution:** The wave aspect is the configuration in I\u221E; the particle aspect is what A selects into A_\u03A9. These are not competing descriptions but descriptions at two levels: possibility space (I\u221E) and actuality (A_\u03A9)."),

      h2("3.3 EPR and Nonlocality"),
      para("**Problem:** Entangled systems exhibit correlations violating Bell inequalities. No local hidden variables can reproduce them."),
      para("**Presupposition:** Correlations require either local hidden variables or nonlocal causal influence."),
      para("**Dissolution:** Entangled states are non-decomposable configurations in I\u221E\u2014their identity cannot be factored into subsystem identities. A_\u03A9 is global; A evaluates joint configurations, not local subsystems independently. Correlations are constitutive constraints on actualization, not causal influences between spatially separated regions."),
      para("Einstein's locality is correct\u2014no superluminal signaling. What fails is separability: the assumption that composite states factor. EPR presupposes that measurement reveals pre-existing local facts. Under LRT, A *constitutes* facts globally. The paradox dissolves because its framing is category-mistaken."),

      ...createImage("epr-dissolution.png", 500, 310, "EPR dissolution under LRT. Left: standard framing assumes local measurement reveals pre-existing facts, generating the paradox. Right: LRT's global A evaluates joint configurations, dissolving the paradox.", 4),

      h2("3.4 Schr\u00F6dinger's Cat"),
      para("**Problem:** Macroscopic superpositions seem to exist before observation."),
      para("**Presupposition:** Superpositions of macroscopic states are physically real configurations."),
      para("**Dissolution:** The superposition |alive\u27E9 + |dead\u27E9 exists in I\u221E\u2014it is representable and evolves unitarily. It is not in A_\u03A9 as a superposition. A selects one L\u2083-admissible outcome. The cat is not both; it is not indeterminate. The paradox arises from treating I\u221E configurations as A_\u03A9 configurations."),

      h2("3.5 Preferred Basis"),
      para("**Problem:** Quantum mechanics does not single out a measurement basis."),
      para("**Presupposition:** Basis selection is a problem about the state."),
      para("**Dissolution:** A selects from the PVM determined by the physical interaction Hamiltonian. The interaction selects the relevant PVM; A selects one outcome from it. No preferred basis is needed in I\u221E because the interaction structure provides it in A_\u03A9."),

      h2("3.6 The Observer"),
      para("**Problem:** Many formulations make observers constitutive."),
      para("**Presupposition:** Quantum states are defined relative to observers."),
      para("**Dissolution:** A_\u03A9 is defined by L\u2083 admissibility, not by observers. Observers are physical systems in A_\u03A9, not constitutive elements. This is strong realism: A selects outcomes independently of observation."),

      new Paragraph({ children: [new PageBreak()] }),

      // Section 4
      h1("4. Discussion"),

      h2("4.1 Comparison to Reconstruction Programs"),
      para("LRT stands in a specific relation to operational reconstruction programs (Hardy 2001; CDP 2011; Masanes-M\u00FCller 2011):"),
      createTable(
        ["Framework", "Starting Point", "What's Unexplained"],
        [
          ["Hardy (2001)", "5 operational axioms", "Why these axioms?"],
          ["CDP (2011)", "6 informational principles", "Why information is primitive?"],
          ["Masanes-M\u00FCller (2011)", "5 physical requirements", "Why these requirements?"],
          ["LRT", "\u03C7 = [L\u2083 : I\u221E : A]", "Grounds the above"]
        ],
        [2800, 3200, 2800]
      ),
      new Paragraph({ spacing: { after: 200 }, children: [] }),
      para("**The subsumption claim:** LRT does not compete with these programs\u2014it subsumes them. Hardy's axioms become derivable given \u03C7. CDP's purification principle follows from Boolean actualization. Masanes-M\u00FCller's requirements are consequences of I\u221E structure."),
      para("**What LRT derives that competitors assume:**"),
      createTable(
        ["Feature", "Competitor Status", "LRT Status"],
        [
          ["Local tomography", "Axiom", "Derived (H1/H2 bridge)"],
          ["Boolean measurement", "Assumed", "Derived (A binary)"],
          ["PVM structure", "Assumed", "Derived (eigenvalue restriction)"],
          ["Born rule", "Derived (Gleason) or assumed", "Derived (Gleason on derived PVM)"],
          ["Temporal structure", "Assumed", "Derived (UNS + Debreu-Nachbin)"]
        ],
        [2800, 3200, 2800]
      ),
      new Paragraph({ spacing: { after: 200 }, children: [] }),

      h2("4.2 Comparison to Interpretations"),
      createTable(
        ["Interpretation", "What LRT Inherits", "What LRT Avoids"],
        [
          ["Copenhagen", "Boolean outcomes", "Observer-dependence"],
          ["Many-Worlds", "Unitary structure, branching in I\u221E", "Branch multiplication"],
          ["Bohmian", "Realism about states", "Pilot wave, primitive nonlocality"],
          ["GRW", "Empirical bet", "Ad hoc parameters"]
        ],
        [2500, 3200, 3100]
      ),
      new Paragraph({ spacing: { after: 200 }, children: [] }),
      para("**MWI subsumption:** Deutsch-Wallace decision-theoretic axioms are derivative of L\u2083. What MWI assumes (ordering, consistency, indifference conditions), LRT derives from Identity, Non-Contradiction, Excluded Middle. The branching structure exists in I\u221E; only one branch is actualized in A_\u03A9."),
      para("**Categorical QM subsumption:** Every \u2020-SMC axiom is derivable from L\u2083. Physics forms dagger categories because logic demands it."),

      h2("4.3 Explanatory Power Inventory"),
      createTable(
        ["Phenomenon", "Standard Status", "LRT Status"],
        [
          ["Born rule", "Postulated / derived", "Derived (Gleason + Boolean A)"],
          ["Measurement problem", "Interpretation-dependent", "Dissolved (A constitutes)"],
          ["Superposition", "Ontologically ambiguous", "Incomplete specification in I\u221E"],
          ["Entanglement", "Nonlocal correlations", "Global L\u2083 constraint"],
          ["Decoherence", "Empirical add-on", "Derived (subsystem L\u2083)"],
          ["Local tomography", "Axiom", "Derived (H1/H2)"],
          ["K=2 (complex field)", "Axiom", "Derived (multiple routes)"],
          ["EPR paradox", "Interpretation-dependent", "Dissolved (A is global)"],
          ["Wave-particle duality", "Mystery", "I\u221E/A_\u03A9 distinction"],
          ["Preferred basis", "Unsolved", "Interaction-determined"],
          ["Observer role", "Constitutive", "None"]
        ],
        [2800, 3200, 2800]
      ),
      new Paragraph({ spacing: { after: 200 }, children: [] }),

      ...createImage("competitor-matrix.png", 550, 360, "Visual comparison of LRT against reconstruction programs (Hardy, CDP, Masanes-M\u00FCller) and interpretations (Copenhagen, MWI, Bohmian, GRW). Green: derived/resolved. Amber: partially addressed. Red: assumed/problematic.", 3),

      h2("4.4 Predictive Constraints"),
      para("LRT rules out:"),
      para("\u2022 Non-Boolean measurement (contradicts L\u2083)"),
      para("\u2022 Finite configuration space (contradicts I\u221E completeness)"),
      para("\u2022 Non-unitary evolution (contradicts actualization continuity)"),
      para("\u2022 K\u22602 fields (contradicts reconstruction chain)"),
      para("\u2022 Super-quantum correlations beyond Tsirelson bound (contradicts \u2102H structure)"),
      para("\u2022 Primitive POVMs (must dilate to PVMs)"),

      ...createImage("entanglement-constraints.png", 500, 350, "Entanglement correlation constraints under LRT. The Tsirelson bound (2\u221A2) emerges from \u2102H structure; super-quantum correlations (PR-box region) are ruled out. The CHSH inequality (classical bound 2) is violated by quantum mechanics but bounded by logical structure.", 6),

      h2("4.5 Falsification and Null Hypothesis"),
      para("**Null hypothesis (H\u2080):** Operational constraints suffice without ontological grounding. QM's axioms are \"just the way things are\" or are operationally motivated but ungrounded."),
      para("**LRT's claim against H\u2080:** The axioms are not arbitrary\u2014they follow from \u03C7. LRT adds explanatory value by answering \"why these axioms?\""),
      para("**Falsification hierarchy:**"),
      createTable(
        ["Level", "Falsifier", "Severity"],
        [
          ["Categorical", "L\u2083 violation in completed physical record", "Fatal to hard core"],
          ["Structural", "Super-quantum correlations, primitive POVMs, non-unitary dynamics", "Revision of argued steps"],
          ["Empirical", "Real QM confirmed over complex (Renou et al.), black hole FC-2b", "Test downstream predictions"]
        ],
        [2000, 5000, 1800]
      ),
      new Paragraph({ spacing: { after: 200 }, children: [] }),
      para("**Lakatosian structure:**"),
      para("\u2022 **Hard core:** \u03C7 \u2261 [L\u2083 : I\u221E : A], bridge equation A_\u03A9 = L\u2083(I\u221E)"),
      para("\u2022 **Protective belt:** Argued steps (local tomography, PVM structure, UNS, continuous time)"),
      para("\u2022 **Progressive predictions:** Complex field selection (confirmed), MWI/categorical subsumption, EPR dissolution"),
      para("**Popper criterion:** Satisfied. Categorical falsifier: stable, reproducible measurement outcome that is both actual and not-actual, or has no determinate truth value. No such violation observed."),

      new Paragraph({ children: [new PageBreak()] }),

      // Section 5
      h1("5. Open Problems"),

      h2("5.1 Current Formalization Status"),
      createTable(
        ["Metric", "Value"],
        [
          ["Build", "SUCCESS (2491 jobs)"],
          ["Axioms", "22"],
          ["Sorries", "0"],
          ["PRIMITIVE", "3 (I, I_infinite, bridge_principle)"],
          ["EXTERNAL", "19 (Gleason, Stone, Hardy, CDP, etc.)"],
          ["REMAINING", "0"]
        ],
        [3000, 5800]
      ),
      new Paragraph({ spacing: { after: 200 }, children: [] }),

      ...createImage("axiom-timeline.png", 500, 350, "Axiom reduction journey from December 2025 to March 2026. Initial count: 55 axioms with 12 sorries. Current: 22 axioms with 0 sorries. Major reductions occurred during Phase 2 (H1/H2 bridge), Phase 4 (Boolean spectrum derivation), and the March 2026 cleanup (31 to 22).", 8),

      ...createImage("dependency-graph.png", 550, 420, "Traceability dependency graph showing 33 claims with 59 directed edges. Node colors indicate claim type (ONT, LOG, ACT, QM, PHY, PRD, OPN, EXT). The graph is acyclic, confirming no circular dependencies in the reconstruction chain.", 9),

      h2("5.2 Axiom Structure"),
      para("All 22 axioms fall into two categories:"),
      createTable(
        ["Category", "Count", "Examples"],
        [
          ["PRIMITIVE", "3", "I (configuration space), I_infinite, bridge_principle"],
          ["EXTERNAL", "19", "Hardy H1/H2, Gleason, Stone, CDP, Wigner, evolution axioms"]
        ],
        [2000, 1500, 5300]
      ),
      new Paragraph({ spacing: { after: 200 }, children: [] }),
      para("**Current status:** Target achieved. Further reduction may be possible when Mathlib adds unbounded operator support."),

      h2("5.3 Extensions"),
      createTable(
        ["Problem", "Type", "Priority"],
        [
          ["Relativistic extension", "Extension", "Medium"],
          ["Quantum field theory", "Extension", "Long-range"],
          ["Fine-structure constant", "Extension", "Speculative"],
          ["Cosmological application", "Extension", "Open"],
          ["Bekenstein-Hawking connection", "Gap", "High"]
        ],
        [4000, 2400, 2400]
      ),
      new Paragraph({ spacing: { after: 200 }, children: [] }),

      new Paragraph({ children: [new PageBreak()] }),

      // Section 6
      h1("6. Conclusion"),
      para("Assuming the TAB result\u2014that physical actuality is constituted by \u03C7 \u2261 [L\u2083 : I\u221E : A], yielding A_\u03A9 = L\u2083(I\u221E)\u2014this paper has derived the complete structure of non-relativistic quantum mechanics. The derivation is formalized in Lean 4 with 22 axioms (3 primitive, 19 external) and zero sorries."),
      para("LRT's contribution is precisely located: not new mathematics, but a new grounding argument for existing mathematics. The reconstruction programs of Hardy, CDP, and Masanes-M\u00FCller are subsumed\u2014their axioms become consequences of \u03C7 rather than postulates. Standing problems dissolve: measurement, EPR, wave-particle duality, Schr\u00F6dinger's cat, preferred basis, the observer. Each arises from a presupposition LRT does not share."),
      para("The null hypothesis\u2014that operational constraints suffice without grounding\u2014is rejected. LRT answers the question reconstruction programs leave open: *why these axioms?*"),
      para("The categorical falsifier remains unobserved: no physical record violates Boolean outcome structure. The structural prediction\u2014complex field selection\u2014is confirmed by Renou et al. (2021). The program is open; the foundation is secure."),

      new Paragraph({ children: [new PageBreak()] }),

      // References
      h1("References"),
      para("Busch, P. (2003). Quantum states and generalized observables: A simple proof of Gleason's theorem. *Physical Review Letters*, 91(12), 120403."),
      para("Chiribella, G., D'Ariano, G. M., and Perinotti, P. (2011). Informational derivation of quantum theory. *Physical Review A*, 84(1), 012311."),
      para("Debreu, G. (1954). Representation of a preference ordering by a numerical function. In R. M. Thrall et al. (Eds.), *Decision Processes* (pp. 159-165). Wiley."),
      para("Fine, K. (2012). Guide to ground. In F. Correia and B. Schnieder (Eds.), *Metaphysical Grounding* (pp. 37-80). Cambridge University Press."),
      para("Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. *Journal of Mathematics and Mechanics*, 6(6), 885-893."),
      para("Hardy, L. (2001). Quantum theory from five reasonable axioms. arXiv:quant-ph/0101012."),
      para("Kochen, S. and Specker, E. P. (1967). The problem of hidden variables in quantum mechanics. *Journal of Mathematics and Mechanics*, 17(1), 59-87."),
      para("Masanes, L. and M\u00FCller, M. P. (2011). A derivation of quantum theory from physical requirements. *New Journal of Physics*, 13(6), 063001."),
      para("Renou, M.-O., et al. (2021). Quantum theory based on real numbers can be experimentally falsified. *Nature*, 600, 625-629."),
      para("Stone, M. H. (1930). Linear transformations in Hilbert space III. *PNAS*, 16(2), 172-175."),

      new Paragraph({ children: [new PageBreak()] }),

      // Appendix A
      h1("Appendix A: QM Primitives to LRT Origins"),
      createTable(
        ["QM Primitive", "Standard Status", "LRT Origin", "Step"],
        [
          ["Hilbert space \u2102H", "Postulated", "Masanes-M\u00FCller", "4"],
          ["Complex field", "Postulated", "Local tomography", "4"],
          ["Pure states", "Postulated", "\u2102H structure", "4"],
          ["Observables", "Postulated", "PVM + spectral theorem", "5"],
          ["Born rule", "Postulated", "Gleason on PVM", "6"],
          ["Tensor products", "Postulated", "Local tomography", "4"],
          ["Unitary evolution", "Postulated", "G-equivariance + Stone", "7-9"],
          ["Schr\u00F6dinger equation", "Postulated", "Stone on U(t)", "10"],
          ["Definite outcomes", "Postulated", "A primitive", "2"]
        ],
        [2400, 2400, 2400, 1000]
      ),
      new Paragraph({ spacing: { after: 200 }, children: [] }),

      // Appendix B
      h1("Appendix B: Axiom Classification"),
      para("**PRIMITIVE (3):** Irreducible LRT commitments"),
      para("\u2022 I : Type* \u2014 configuration space"),
      para("\u2022 I_infinite \u2014 I\u221E completeness"),
      para("\u2022 bridge_principle \u2014 \u03C7 grounds A_\u03A9"),
      new Paragraph({ spacing: { after: 200 }, children: [] }),
      para("**EXTERNAL (19):** Established mathematics, axiomatized for Lean efficiency"),
      para("\u2022 Hardy H1/H2 (2)"),
      para("\u2022 Gleason theorem (3)"),
      para("\u2022 Stone theorem (2)"),
      para("\u2022 CDP results (3)"),
      para("\u2022 Wigner theorem (1)"),
      para("\u2022 Evolution/dynamics (4)"),
      para("\u2022 Supporting lemmas (4)"),
      new Paragraph({ spacing: { after: 200 }, children: [] }),
      para("**REMAINING (0):** All derivation targets achieved"),
      para("\u2022 Axiom count reduced from 55 (Dec 2025) to 22 (Mar 2026)"),
      para("\u2022 Further reduction possible with Mathlib unbounded operator support"),
      new Paragraph({ spacing: { after: 200 }, children: [] }),

      ...createImage("axiom-treemap.png", 450, 280, "Visual breakdown of 22 axioms by classification. PRIMITIVE (3): irreducible LRT commitments. EXTERNAL (19): established mathematics imported for Lean efficiency. REMAINING (0): all derivation targets achieved.", 2),
    ]
  }]
});

// Write file
const outputPath = path.join(__dirname, 'LRT-MASTER-v2.0.docx');
Packer.toBuffer(doc).then(buffer => {
  fs.writeFileSync(outputPath, buffer);
  console.log(`Created: ${outputPath}`);
}).catch(err => {
  console.error('Error:', err);
  process.exit(1);
});
