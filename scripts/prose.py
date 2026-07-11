# -*- coding: utf-8 -*-
# This file is exec'd inside build_docx.py; it may use: doc, add_body, add_code,
# add_theorem, total, tcount, lcount, decls, headers, and the docx helpers.

def H(text, level):
    return doc.add_heading(text, level=level)

# ---------- Abstract ----------
H('Abstract', 1)
add_body(
    'This document gives a systematic and detailed introduction to the Recursive '
    'Generative Framework (RGF) and its internal transfinite set theory upgrade RGF 2.0, '
    'together with a complete catalogue of every theorem in the entire Lean 4 formalization '
    'library. RGF takes "recursive generation" as its single primitive: every structure is '
    'regarded as the product of iterating one action, step = modify ∘ generate (first '
    '"generate" a candidate object, then "modify" it according to an invariant), along some '
    'time flow. Starting from this primitive, the system builds, on top of Lean 4 + Mathlib, '
    'the natural numbers, integers, rationals, and reals in turn, and further unfolds a '
    'mathematical backbone including analysis, algebra, category theory, spectral theory, '
    'graph theory, and topology. On the physics side, the same substrate is unfolded via '
    'Recursive Constitutive Dynamics (RCD) into the emergence of spacetime, gravity, gauge '
    'structure, and the Standard Model parameter spectrum.')
add_body(
    'RGF 2.0 is the formal realization of four technical routes addressing the question of '
    '"how to upgrade RGF\'s internal set theory seamlessly from a finite system (ZF−∞, of '
    'strength roughly PA) to full ZFC": lifting the encoding domain (W-type tree quotients), '
    'an internal cumulative hierarchy with a reflection principle, a Boolean-valued model with '
    'a forcing skeleton, and a transfinite generative flow (transfinite recursion, the Hartogs '
    'function, well-ordering, and the axiom of choice). All conclusions are genuine machine '
    'proofs: the whole library passes lake build, has no sorry (except for a few finite Coxeter '
    'group cardinality gaps honestly marked OPEN in the source), no custom axiom, and no '
    '@[implemented_by], and the kernel axiom footprint of the flagship propositions, audited '
    'via #print axioms, lies solely within the standard allowed set.')
add_body('Keywords: Recursive Generative Framework; Recursive Constitutive Dynamics; formalized '
         'mathematics; Lean 4; internal set theory; ZFC; W-types; Boolean-valued models; forcing; '
         'transfinite recursion; emergence; machine verification.', italic=True)

# ---------- Part I ----------
doc.add_page_break()
H('Part I  Overview of the System', 1)

H('1. Introduction: one primitive, one system', 2)
add_body(
    'RGF\'s starting point is a philosophically minimal, mathematically fully formalizable '
    'stance: every structure is the product of a single action, "recursive generation". The '
    'generative action is written step = modify ∘ generate — first "generate" a new candidate '
    'object, then "modify" it according to an invariant. The natural numbers are the first '
    'objects this action produces (zero | succ induction); the integers, rationals, and reals '
    'are then produced stepwise via standard algebraic constructions; higher up, analysis, '
    'algebra, category theory, spectral theory, graph theory, and topology are all products of '
    'the same generative action at different levels.')
add_body(
    'On the physics side, RGF\'s dynamical realization is called Recursive Constitutive '
    'Dynamics (RCD): iterating discrete "lock-membrane / recovery" rules along a time flow, '
    'under coarse-graining and the renormalization flow, yields the emergence of continuous '
    'spacetime, gravity, gauge structure, and the Standard Model parameter spectrum. RGF and '
    'RCD share the same verified mathematical substrate, so the "mathematical foundations" and '
    'the "physical phenomenology" close up within one and the same formal system.')

H('2. System architecture and the four tiers', 2)
add_body('The entire system is a Lean library named RGF, organized into four thematic tiers, '
         'with the directory structure in strict correspondence with the namespaces:')
add_body('· Tier 1, the generative backbone (RGF.Generative.*): the generative primitive, '
         'locking, uniqueness, and metatheory.', before=0, after=0)
add_body('· Tier 2, the mathematical products (RGF.Math.*): internal number systems, set '
         'theory, analysis, category theory, spectral theory, graph theory, algebra, topology — '
         'all products of the Tier-1 generative action.', before=0, after=0)
add_body('· Tier 3, the physical dynamics (RGF.Physics.*): universal physical dynamics and '
         'emergence (the formalization of RCD).', before=0, after=0)
add_body('· Tier 4, phenomenology (RGF.Phenomenology.*): Standard Model phenomenology and the '
         'test/audit suite.', before=0, after=0)
add_body('There is in addition an applications tier (RGF.Applications.*), which applies the '
         'generative dynamics to concrete problems such as ergodicity, orbit counting, and '
         'intrinsic symmetry.')
add_body(
    'The tiers maintain a strict one-way dependency: the neutral generative core '
    '(RGF.Generative.Core.*) of Tier 1 together with the mathematical substrate (RGF.Math.*) '
    'form the system\'s Tier 1, whose transitive import closure contains no physics / '
    'phenomenology module. This "one-way independence of Tier 1" is checked mechanically by a '
    'script (check_tier_boundary.py), with a counterexample self-test guaranteeing that the '
    'gate is effective, so that "the mathematical foundations do not depend on physical '
    'assumptions" is not a slogan but a verifiable architectural invariant.')

H('3. The generative backbone and the internal number systems', 2)
add_body(
    'The generative primitive first builds the natural numbers RGFNat (zero | succ induction), '
    'then produces stepwise, via standard algebraic constructions, the integers RGFInt, the '
    'rationals RGFRat, and the reals RGFReal′. RGFReal′ is constructed from Cauchy sequences of '
    'RGF rationals and is proved to be entirely consistent with the standard reals:')
add_code('noncomputable def orderedRingEquivReal : RGFReal′ ≃+*o ℝ', size=10)
add_body(
    'This ordered-ring isomorphism (RGF.RGFReal′.orderedRingEquivReal) shows that RGF\'s '
    'internally generated reals are structurally indistinguishable from the classical reals, so '
    'that the analytic objects built from the generative primitive can interface seamlessly with '
    'Mathlib\'s real analysis. This makes RGF\'s "self-built number system" both an ontological '
    'generative product and mathematically equivalent to the standard reals — the first '
    'cornerstone of the whole system.')

H('4. Internal transfinite set theory: from generative trees to full ZFC (the four routes of RGF 2.0)', 2)
add_body(
    'RGF 1.0\'s internal set theory uses Ackermann encoding to map sets to finite binary '
    'integers, and can therefore only accommodate hereditarily finite sets (HF), with '
    'consistency strength roughly Peano Arithmetic (PA). RGF 2.0, through a fundamental '
    'reconstruction of the "encoding domain, generative primitive, and logical value domain", '
    'upgrades the internal set theory seamlessly from a finite system to full ZFC. The following '
    'four routes correspond one-to-one with modules in the system.')

H('Route I  Lifting the encoding domain: from arithmetic encoding to lossless W-types', 3)
add_body(
    'The encoding domain at the core of the set theory uses labelled well-founded inductive '
    'trees (W-types): a set is a branching tree, its "extensional equality" given by a '
    'bidirectional embedding between trees, and the membership relation Mem₂ defined on the '
    'branches of trees. Taking the quotient of these trees by the equivalence relation yields '
    'the internal set universe RGFSet₂. At this point the reals are no longer the carrier of an '
    'encoding of sets, but an ordinary internal object within the tree-shaped set universe. Over '
    'this universe, the system proves in one go the complete ten ZFC axioms:')
add_code('theorem RGF2_models_ZFC :\n'
         '  (extensionality) ∧ (empty set) ∧ (pairing) ∧ (union) ∧ (power set) ∧\n'
         '  (separation schema) ∧ (replacement schema) ∧ (foundation) ∧ (infinity) ∧ (choice)', size=9)
add_body('Corresponding modules: RGF/Math/SetTheory/RGF2/Core/WType.lean, RGF2.lean, Master.lean. '
         'The theorem infinity_strict_upgrade further shows that RGF 2.0 satisfies the axiom of '
         'infinity, while the hereditarily finite core of RGF 1.0 provably satisfies its negation, '
         'confirming that this is a strict upgrade.')

H('Route II  Internal universe hierarchies and the reflection principle', 3)
add_body(
    'To overcome the "low consistency strength" limitation imposed by Gödel incompleteness, the '
    'system constructs a cumulative hierarchy Vhier inside RGF: V₀=∅, V(α+1)=P(Vα), and limit '
    'levels take unions Vλ=⋃_{β<λ}Vβ. Around it are formalized exhaustiveness, the union equation '
    'at limit levels, a rank calculus, and the Montague–Lévy reflection principle, and Lean 4\'s '
    'multi-level universe mechanism is used to express Vω and even the inaccessible-cardinal '
    'universe Vκ. The theorem RGF2_inaccessible_gives_ZFC_model honestly writes the conclusion in '
    'conditional form: if a strongly inaccessible cardinal exists, then a transitive model of ZFC '
    'exists — placing "ZFC + inaccessible" above ZFC, rather than claiming that RGF itself '
    'transcends ZFC.')
add_body('Corresponding modules: RGF/Math/SetTheory/RGF2/Hierarchy/ (Cumulative, Reflection, '
         'Inaccessible, Transfinite, HereditarilyFinite, etc.).')

H('Route III  Widening the logical value domain: from two-valued logic to Boolean-valued models', 3)
add_body(
    'To eliminate model rigidity and gain the flexibility of forcing, the system generalizes the '
    'value domain of the membership relation from the two-valued Prop to an arbitrary complete '
    'Boolean algebra B, constructing the Boolean-valued universe BSet B (i.e. V^B). The theorem '
    'RGF2_boolean_valued_ZFC_full proves that each ZFC axiom holds at the Boolean value ⊤; '
    'RGF2_forcing_relation_calculus gives the standard calculus laws of the forcing relation ⊩ᴮ; '
    'and IndependenceFamily(Infinite) gives the combinatorial skeleton for independence '
    'statements (such as ¬CH). Thereby, the independence statements of set theory can be '
    'discussed directly within the Boolean-valued model.')
add_body('Corresponding modules: RGF/Math/SetTheory/RGF2/Boolean/ (Model, ValuedZFC, Forcing, '
         'ForcingRelation, ChoiceReplacement, IndependenceFamily, IndependenceFamilyInfinite).')

H('Route IV  Internalizing transfinite recursion and the well-ordering principle in the generative operator', 3)
add_body(
    'RGF\'s current "generative" primitive proceeds along a natural-number or real time axis, and '
    'is epistemologically confined within ℵ₀ or 2^ℵ₀ steps. Route IV generalizes the iteration '
    'operator to a transfinite time flow, so that the generative action can proceed along an '
    'arbitrary well-ordered set by transfinite induction; and it formalizes the Hartogs theorem '
    'on RGF trees — for any set X producing an ordinal larger than X — on which basis the '
    'well-ordering theorem and the (transfinite) axiom of choice are proved inside RGF. Theorems '
    'such as tfIterate_omega_eq_lim further prove that the limit-stage rule is genuinely '
    '"load-bearing" (changing the limit rule changes the conclusion), dispelling the doubt that '
    'the limit level is a trivial renaming.')
add_body('Corresponding modules: RGF/Math/SetTheory/RGF2/Hierarchy/Transfinite.lean, '
         'TransfiniteLimitLoadBearing.lean, Core/InternalOrdinal.lean, Core/InternalCardinal.lean.')

H('5. Locking, uniqueness, and honesty', 2)
add_body(
    'A central topic of the generative backbone is "phase locking": under what conditions a '
    'recursive system locks onto a specific symmetry and dimension. The system formalizes the Z5 '
    'phase-locking mechanism and gives an honest, non-inflated conclusion to the key question of '
    '"why 5":')
add_code('theorem k_five_conditional_on_solvability_criterion :\n'
         '  (∀ sys, FiveLockingCondition sys → sys.k = 5) ∧\n'
         '  (∀ sys, EmergenceCondition sys ↔ ¬ IsSolvable (Equiv.Perm (Fin sys.k)))', size=9)
add_body(
    'This theorem honestly notes that, once the "solvability criterion" is granted, k=5 is '
    'uniquely forced by minimality; but the criterion itself is introduced by definition. '
    'Similarly, the three-dimensional locking of space comes from the algebraic self-duality '
    'dim 𝔰𝔬(d)=d (i.e. d(d−1)=2d), which for d≥1 holds if and only if d=3. The uniqueness tier '
    '(RGF.Generative.Uniqueness.*) systematically distinguishes "provable" from "not provable", '
    'separating modelling assumptions from derived conclusions.')

H('6. Recursive Constitutive Dynamics (RCD) and physical emergence', 2)
add_body('On the shared mathematical substrate, RCD iterates discrete lock-membrane rules along a '
         'time flow and examines their effective emergence under coarse-graining / renormalization '
         'flow. The system gives machine-verified cores for a number of physical propositions, for '
         'example:')
add_body('· Spatial-dimension locking spatial_dimension_three; the quantum-correlation upper bound '
         'chsh_tsirelson_bound (the Tsirelson bound 2√2).', before=0, after=0)
add_body('· Lattice to continuum: deriving time-domain recursion equations from lock-membrane '
         'lattice rules, including diffusion coefficient, coarse-graining noise, and the FORS '
         'kernel.', before=0, after=0)
add_body('· Planck scale planckLength_ratio_bounds; recursive/spiral scaling laws with cosmological '
         'emergence and the dark-energy coefficient.', before=0, after=0)
add_body('· Strings and gravitons, the unlocking-mode phase transition, and the information-'
         'localization phase diagram of time-domain coarse-graining.', before=0, after=0)

H('7. Standard Model phenomenology', 2)
add_body('The phenomenology tier pushes the above structures to the Standard Model parameter '
         'spectrum. Gauge-group emergence yields a verifiable quantitative conclusion — the '
         'Weinberg angle at the GUT scale:')
add_code('theorem weinberg_angle_gut : (∑ i, weakIsospin i ^2)/(∑ i, charge i ^2) = 3/8', size=10)
add_body('This theorem proves that the ratio of the sum of squared weak isospins to the sum of '
         'squared charges is exactly 3/8, i.e. the classical sin²θ_W = 3/8. This tier also '
         'contains propositions such as hypercharge tracelessness, the five-pole phase sum, and '
         'neutrino mixing (e.g. the falsification of tribimaximal θ₁₃), together with a test/audit '
         'suite.')

H('8. Verification methodology and trustworthiness', 2)
add_body('The system treats "trustworthiness" itself as a first-class goal, adopting the following '
         'mechanisms:')
add_body('· No sorry, no custom axiom, no @[implemented_by]: the whole library passes lake build, '
         'and all conclusions are genuine machine proofs (the only honestly marked OPEN gaps are '
         'the cardinalities of the finite Coxeter groups |W_H3|, |W_H4| in CoxeterFiveFold.lean, '
         'for which Mathlib does not yet contain the corresponding classification theorem).',
         before=0, after=0)
add_body('· Auditable axiom footprint: the flagship propositions, verified via #print axioms, '
         'depend only on propext, Classical.choice, Quot.sound (with a few finite decisions '
         'additionally using Lean.ofReduceBool).', before=0, after=0)
add_body('· Mechanized architectural invariant: the one-way independence of Tier 1 is checked by a '
         'script, with a counterexample self-test guaranteeing the gate is effective.',
         before=0, after=0)
add_body('· Honesty theorems: modelling assumptions not yet closed are explicitly marked with '
         'conditional theorems and the Iff.rfl form, without passing off a definition as a '
         'derivation.', before=0, after=0)

H('9. Scale statistics (extracted at runtime from the source tree)', 2)
add_body(f'· Total number of source files: 305 .lean files.', before=0, after=0)
add_body(f'· Total number of theorems/lemmas: {total} (of which {tcount} theorems and {lcount} '
         f'lemmas).', before=0, after=0)
add_body('· Organized into 4 thematic tiers + an applications tier, with 23 subdirectories in '
         'total (see Part II for the directory-by-directory, file-by-file catalogue).',
         before=0, after=0)
add_body('Note: Part II below lists, file by file, the name and Lean type signature of every '
         'theorem/lemma (truncated to just before the proof start :=), attaching the original '
         'description when the source carries a docstring, so that the reader can search and '
         'cross-check them one by one in the source.', italic=True)

# ============ TIER / DIR intros used by build_docx.py ============
TIER_INTRO = {
 'RGF/Generative': 'The generative backbone is Tier 1 of the system, formalizing the "recursive '
    'generation" primitive itself and its consequences: the core syntax and invariants, the '
    'phase/dimension locking mechanism, the necessity and uniqueness of the initial assumptions, '
    'and the metatheory concerning the falsifiability, universality, etc., of the generative '
    'predicate.',
 'RGF/Math': 'The mathematical-products tier is the direct product of the Tier-1 generative '
    'action: internal number systems and the reals, the internal transfinite set theory RGF 2.0, '
    'analysis, algebra, category theory, spectral theory, graph theory, and topology. Together '
    'with the generative core, this tier forms the Tier 1 that does not depend on physical '
    'assumptions.',
 'RGF/Physics': 'The physical-dynamics tier is the formalization of Recursive Constitutive '
    'Dynamics (RCD): coarse-graining, the renormalization group, scaling laws, the lattice-to-'
    'continuum limit, spacetime and gravity emergence, the Planck scale and cosmology, etc.',
 'RGF/Phenomenology': 'The phenomenology tier pushes the generative dynamics to the Standard '
    'Model parameter spectrum: gauge-group emergence, the Weinberg angle, neutrino mixing, the '
    'Koide relation, etc., equipped with a test and audit suite.',
 'RGF/Applications': 'The applications tier applies the generative dynamics to concrete '
    'mathematical problems: constructive ergodicity, orbit counting, linearized spectra, '
    'intrinsic symmetry, Babai-type weak results, etc.',
}

DIR_INTRO = {
 'RGF/Generative/Assembly': 'Assembly tier: assembles the core propositions (the six main '
    'propositions, Proposition C, etc.) into overall conclusions and a simplified core.',
 'RGF/Generative/Bridge': 'Bridge tier: connects the abstract RGF dynamics with standard Mathlib '
    'structures, including two-layer/three-layer universality, symmetry derivation, portable RGF '
    'states, and dynamical properties.',
 'RGF/Generative/Core': 'Generative core: the recursive syntax, basic definitions and invariants, '
    'the evaluation functional, the RGF axioms and core propositions (the Paper1 RCE foundations, '
    'the self-referential soliton, etc.). This is the neutral bottom layer of the whole system.',
 'RGF/Generative/Locking': 'Locking tier: the complete theory of phase locking and dimension '
    'locking — Z5 phase locking, five-fold symmetry, the critical ratio, three-dimensional '
    'uniqueness, mode decomposition and mode locking, five-fold locking uniqueness, Penrose '
    'quasicrystals / K-theory, etc.',
 'RGF/Generative/Meta': 'Metatheory tier: falsifiability of the generative predicate, RGF '
    'universality, algorithmic information, analytic number theory, Lomb–Scargle and numerical '
    'verification, the current status of the relation between RGF and the Riemann hypothesis, etc.',
 'RGF/Generative/Uniqueness': 'Uniqueness tier: the necessity and minimality of the initial '
    'assumptions, the necessity of the complex base field, coverage, G1 exclusivity, realizability '
    'obstructions, stability uniqueness — systematically distinguishing "provable" from "not '
    'provable".',
 'RGF/Math/Algebra': 'Algebra: the simple group A5, affine Kac–Moody, algebraic geometry, Coxeter '
    'five-fold symmetry, the crystallographic restriction, dihedral groups, finite-group Fourier '
    'analysis, Lie-algebra embeddings, noncommutative geometry, PSL(2,7), Clifford chirality, '
    'modular forms and representation theory, etc.',
 'RGF/Math/Analysis': 'Analysis: constructive Feynman–Kac and ODEs, the continuum limit, '
    'convergence theory, the fundamental theorem of calculus, functional analysis, Γ-convergence, '
    'inductive limits, measure and integration, RGF continuity/derivative/limit, strict '
    'quasiconvexity, etc.',
 'RGF/Math/Category': 'Category theory: dynamical HoTT and its flow, equivariant functors, the '
    'fixed-point subcategory, the forgetful functor, the generative-dynamics category and '
    'generative refinement, the RGF category.',
 'RGF/Math/Graph': 'Graph theory: the Frucht theorem (general/RGF versions), graph automorphisms, '
    'orbit classification and pairing, the Petersen graph, quantum orbit pairing, Burnside, '
    'colouring, planarity, Ramsey, t-designs, the Turán graph.',
 'RGF/Math/Real': 'Internal number systems and the reals: RGFNat/Int/Rat and their order and '
    'field structure, Cauchy sequences and Dedekind cuts, Banach contraction, the ordered-ring '
    'isomorphism between RGFReal′ and the standard reals, internal infinity, integration, etc. '
    'This is the first cornerstone of the system.',
 'RGF/Math/SetTheory': 'Set theory main directory: the RGF–ZFC comparison, consistency strength, '
    'the Galois connection, Grothendieck universes, the ZF baseline, and the entry point to the '
    'RGF 2.0 subsystem.',
 'RGF/Math/SetTheory/RGF2': 'The main body of RGF 2.0: the W-type tree-quotient universe RGFSet₂, '
    'the master theorem Master for the ten ZFC axioms, the emergent ω, the generative bridge, and '
    'the honest labelling of relative strength.',
 'RGF/Math/SetTheory/RGF2/Boolean': 'Boolean-valued model (Route III): the complete-Boolean-'
    'algebra-valued universe V^B, Boolean-valued ZFC, the forcing relation and its calculus, '
    'choice and replacement, and the combinatorial skeleton of the ¬CH independence family.',
 'RGF/Math/SetTheory/RGF2/Core': 'RGF 2.0 kernel: the W-type definition, internal ordinals and '
    'internal cardinals, the symmetric-difference group structure.',
 'RGF/Math/SetTheory/RGF2/Hierarchy': 'Cumulative hierarchy and transfinite (Routes II and IV): '
    'the Vhier cumulative hierarchy, the reflection principle, inaccessible cardinals and the ZFC '
    'model, transfinite recursion and load-bearing limit stages, the hereditarily finite level.',
 'RGF/Math/Spectral': 'Spectral theory: the Cheeger inequality, the heat kernel, the Laplacian, '
    'the Rayleigh quotient, spectral-gap dynamics, spectral methods, the Standard Model spectral '
    'triple, the spectral-reduction conjecture.',
 'RGF/Math/Topology': 'Topology: algebraic topology, boundary paths, the cobordism hypothesis, '
    'constructive TDA, de Rham, differential geometry, the Euler characteristic, the filling '
    'radius, the Fisher metric, persistent homology, Regge calculus, topological emergence.',
 'RGF/Physics/Dynamics': 'Dynamics: coarse-graining and the renormalization group, anomalous '
    'scaling, bilayer duality, conformal field theory, detailed balance, discrete gauge theory '
    'and the trace formula, the fault-tolerance threshold, the hydrodynamic limit, KPZ and its '
    'derivation, mixing time, the phase diagram, regularity structures, stochastic PDE FRG, the '
    'toric code, the Yau relative entropy, etc.',
 'RGF/Physics/Emergence': 'Emergence: the complete derivation chain and uniqueness, '
    'complexity/energy/entropy emergence, FORS energy first principles, geometric reduction, '
    'lattice to continuum and dispersion, spacetime and gravity (Paper2), the Planck scale '
    '(Paper7), cosmology (Paper9), strings and gravitons, recursively generated constants, etc.',
 'RGF/Phenomenology/StandardModel': 'Standard Model: the α/β parameters, detuning analysis, grand '
    'unification, the Koide extension, non-Hermitian lepton phases, neutrino predictions and σ '
    'deviations, gauge emergence and partition (Paper6), Planck phenomenology, gauge ratios, '
    'generated constants, thresholds, ζ regularization, the 26-parameter spectrum, etc.',
 'RGF/Phenomenology/TestSuite': 'Test and audit suite: the full audit, the deduplication audit, '
    'the native_decide audit, the KAM Diophantine criterion, original mathematics and frontier '
    'propositions, responses to criticism, and the sets of theorems newly added / appended in '
    'each batch.',
}
