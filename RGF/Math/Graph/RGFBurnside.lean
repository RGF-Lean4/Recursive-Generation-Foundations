/-
  Burnside's lemma and Pólya counting
  Lean support for paper ten

  Formalises the orbit-counting theory of finite group actions,
  connecting to the notion of symmetry factor in recursive generation theory.
-/

import Mathlib

open Finset BigOperators MulAction

/-! ## 1. Burnside's lemma -/

/-
Burnside's lemma (the Cauchy-Frobenius lemma):
    number of orbits = (1/|G|) ∑_{g ∈ G} |Fix(g)|

    Here we give the precise equational form of the fixed-point sum and the number of orbits:
    ∑_{g ∈ G} |Fix(g)| = |G| × |X/G|
-/
theorem burnside_lemma {G : Type*} [Group G] [Fintype G]
    {X : Type*} [MulAction G X] [Fintype X] [DecidableEq X]
    [Fintype (orbitRel.Quotient G X)]
    [∀ g : G, DecidablePred (fun x : X => g • x = x)] :
    ∑ g : G, Fintype.card { x : X // g • x = x } =
    Fintype.card G * Fintype.card (orbitRel.Quotient G X) := by
  convert MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X using 1;
  · congr! 2;
  · exact mul_comm _ _

/-! ## 2. Basic properties of fixed-point sets -/

/-
the fixed-point set of the identity element is the whole set
-/
theorem fixedPoints_one {G : Type*} [Group G]
    {X : Type*} [MulAction G X] [Fintype X]
    [DecidablePred (fun x : X => (1 : G) • x = x)] :
    Fintype.card { x : X // (1 : G) • x = x } = Fintype.card X := by
  simp +decide

/-! ## 3. Cyclic group actions -- necklace counting -/

/-- the number of ways to colour a necklace of k beads with n colours (up to cyclic equivalence) -/
noncomputable def necklaceCount (n k : ℕ) : ℕ :=
  if k = 0 then 1
  else (∑ d ∈ Nat.divisors k, Nat.totient (k / d) * n ^ d) / k

/-- number of 2-colour 5-bead necklaces = 8 -/
theorem necklace_2_5 : necklaceCount 2 5 = 8 := by
  simp [necklaceCount]
  decide

/-- number of 2-colour 6-bead necklaces = 14 -/
theorem necklace_2_6 : necklaceCount 2 6 = 14 := by
  simp [necklaceCount]
  decide

/-! ## 4. The Burnside expansion of the symmetry factor -/

/-- symmetry factor as the ratio of orbit length to group order (using explicit parameters) -/
noncomputable def symmetryFactorBurnside'
    (orbitCard groupCard : ℕ) : ℚ :=
  (orbitCard : ℚ) / (groupCard : ℚ)

/-- relation between the symmetry factor and the stabiliser (using the orbit-stabiliser theorem) -/
theorem symmetryFactor_eq_inv_stab'
    (orbitCard stabCard groupCard : ℕ)
    (hstab : 0 < stabCard)
    (hgroup : 0 < groupCard)
    (horbit_stab : orbitCard * stabCard = groupCard) :
    symmetryFactorBurnside' orbitCard groupCard =
    (1 : ℚ) / (stabCard : ℚ) := by
  unfold symmetryFactorBurnside'
  rw [div_eq_div_iff (by positivity) (by positivity)]
  simp; exact_mod_cast horbit_stab

/-! ## 5. Explicit counting for the D₅ group action -/

/-- D₅ (the dihedral group, order=10) acting on colourings of the vertices of a regular pentagon.
    The number of equivalence classes under colouring with n colours. -/
noncomputable def dihedralColorings (n : ℕ) : ℕ :=
  -- Burnside formula: 1/10 × (n^5 + 4n + 5n^3) (rotations + reflections)
  (n ^ 5 + 4 * n + 5 * n ^ 3) / 10

/-- number of 2-colour D₅-equivalent colourings = 8 -/
theorem dihedral5_2colors : dihedralColorings 2 = 8 := by
  simp [dihedralColorings]

/-- number of 3-colour D₅-equivalent colourings = 39 -/
theorem dihedral5_3colors : dihedralColorings 3 = 39 := by
  simp [dihedralColorings]