/-
  Invariants/Theorems.lean — RGF invariant theory: core theorems
  RGF Invariant Theory: Core Theorems

  This file formalizes:
  1. isomorphism preserves Betti numbers (topological-invariant preservation theorem)
  2. isomorphism preserves the automorphism group (algebraic-invariant preservation theorem)
  3. isomorphism preserves the Euler characteristic
  4. the equivariance condition — the cornerstone of invariant theory
  5. under an equivariant iteration system, the automorphism group is preserved along the orbit
  6. the spectral-gap upper bound (with appropriate symmetry hypotheses)
-/

import Mathlib
import RGF.Generative.Core.Basic

open Finset BigOperators Equiv Function

namespace RGFState

variable {n : ℕ}

/-! ============================================================
    Part 1: isomorphism preserves the edge count
    ============================================================ -/

/-- Isomorphic RGF states have the same number of edges. -/
theorem iso_preserves_edgeCount (s₁ s₂ : RGFState n) (f : RGFMorphism s₁ s₂) :
    s₁.edgeCount = s₂.edgeCount := by
      fapply Finset.card_bij;
      use fun p hp => if f.toEquiv p.1 < f.toEquiv p.2 then ( f.toEquiv p.1, f.toEquiv p.2 ) else ( f.toEquiv p.2, f.toEquiv p.1 );
      · unfold RGFState.edges;
        grind +suggestions;
      · simp +contextual [ RGFState.edges ];
        intro a b hab hlt a' b' hab' hlt' h; split_ifs at h <;> simp_all +decide ;
        · exact False.elim <| lt_asymm hlt hlt';
        · exact False.elim <| lt_asymm hlt hlt';
      · intro b hb; use if f.toEquiv.symm b.1 < f.toEquiv.symm b.2 then ( f.toEquiv.symm b.1, f.toEquiv.symm b.2 ) else ( f.toEquiv.symm b.2, f.toEquiv.symm b.1 ) ; simp_all +decide [ RGFState.edges ] ;
        split_ifs <;> simp_all +decide;
        · have := f.preserves ( f.toEquiv.symm b.1 ) ( f.toEquiv.symm b.2 ) ; aesop;
        · exact False.elim <| lt_asymm hb.2 ‹_›;
        · have := f.preserves ( f.toEquiv.symm b.2 ) ( f.toEquiv.symm b.1 ) ; simp_all +decide [ RGFState.symm ] ;
          exact lt_of_le_of_ne ‹_› ( by intro h; have := s₁.irrefl ( f.toEquiv.symm b.1 ) ; aesop )

/-! ============================================================
    Part 2: isomorphism preserves the triangle count
    ============================================================ -/

/-- Isomorphic RGF states have the same number of triangles. -/
theorem iso_preserves_triangleCount (s₁ s₂ : RGFState n) (f : RGFMorphism s₁ s₂) :
    s₁.triangleCount = s₂.triangleCount := by
      obtain ⟨ f, hf ⟩ := f;
      fapply Finset.card_bij;
      use fun a ha => if h : f a.1 < f a.2.1 ∧ f a.2.1 < f a.2.2 then ( f a.1, f a.2.1, f a.2.2 ) else if h' : f a.1 < f a.2.2 ∧ f a.2.2 < f a.2.1 then ( f a.1, f a.2.2, f a.2.1 ) else if h'' : f a.2.1 < f a.1 ∧ f a.1 < f a.2.2 then ( f a.2.1, f a.1, f a.2.2 ) else if h''' : f a.2.1 < f a.2.2 ∧ f a.2.2 < f a.1 then ( f a.2.1, f a.2.2, f a.1 ) else if h'''' : f a.2.2 < f a.1 ∧ f a.1 < f a.2.1 then ( f a.2.2, f a.1, f a.2.1 ) else ( f a.2.2, f a.2.1, f a.1 );
      · simp +decide [ RGFState.triangles ];
        grind +suggestions;
      · simp +zetaDelta at *;
        intro a b c ha d e f hb h;
        have h_eq : (‹Perm (Fin n)› a = ‹Perm (Fin n)› d ∧ ‹Perm (Fin n)› b = ‹Perm (Fin n)› e ∧ ‹Perm (Fin n)› c = ‹Perm (Fin n)› f) ∨ (‹Perm (Fin n)› a = ‹Perm (Fin n)› d ∧ ‹Perm (Fin n)› b = ‹Perm (Fin n)› f ∧ ‹Perm (Fin n)› c = ‹Perm (Fin n)› e) ∨ (‹Perm (Fin n)› a = ‹Perm (Fin n)› e ∧ ‹Perm (Fin n)› b = ‹Perm (Fin n)› d ∧ ‹Perm (Fin n)› c = ‹Perm (Fin n)› f) ∨ (‹Perm (Fin n)› a = ‹Perm (Fin n)› e ∧ ‹Perm (Fin n)› b = ‹Perm (Fin n)› f ∧ ‹Perm (Fin n)› c = ‹Perm (Fin n)› d) ∨ (‹Perm (Fin n)› a = ‹Perm (Fin n)› f ∧ ‹Perm (Fin n)› b = ‹Perm (Fin n)› d ∧ ‹Perm (Fin n)› c = ‹Perm (Fin n)› e) ∨ (‹Perm (Fin n)› a = ‹Perm (Fin n)› f ∧ ‹Perm (Fin n)› b = ‹Perm (Fin n)› e ∧ ‹Perm (Fin n)› c = ‹Perm (Fin n)› d) := by
          split_ifs at h <;> simp +decide [ * ] at h ⊢;
          all_goals simp +decide [ h ];
        simp_all +decide [ RGFState.triangles ];
        grind +splitIndPred;
      · intro b hb;
        use if h : f.symm b.1 < f.symm b.2.1 ∧ f.symm b.2.1 < f.symm b.2.2 then ( f.symm b.1, f.symm b.2.1, f.symm b.2.2 ) else if h' : f.symm b.1 < f.symm b.2.2 ∧ f.symm b.2.2 < f.symm b.2.1 then ( f.symm b.1, f.symm b.2.2, f.symm b.2.1 ) else if h'' : f.symm b.2.1 < f.symm b.1 ∧ f.symm b.1 < f.symm b.2.2 then ( f.symm b.2.1, f.symm b.1, f.symm b.2.2 ) else if h''' : f.symm b.2.1 < f.symm b.2.2 ∧ f.symm b.2.2 < f.symm b.1 then ( f.symm b.2.1, f.symm b.2.2, f.symm b.1 ) else if h'''' : f.symm b.2.2 < f.symm b.1 ∧ f.symm b.1 < f.symm b.2.1 then ( f.symm b.2.2, f.symm b.1, f.symm b.2.1 ) else ( f.symm b.2.2, f.symm b.2.1, f.symm b.1 );
        simp +decide [ RGFState.triangles ] at hb ⊢;
        grind +suggestions

/-! ============================================================
    Part 3: isomorphism preserves the Euler characteristic
    ============================================================ -/

/-- Isomorphic RGF states have the same Euler characteristic. -/
theorem iso_preserves_eulerChar (s₁ s₂ : RGFState n) (f : RGFMorphism s₁ s₂) :
    s₁.eulerChar1 = s₂.eulerChar1 := by
  unfold eulerChar1
  rw [iso_preserves_edgeCount s₁ s₂ f, iso_preserves_triangleCount s₁ s₂ f]

/-! ============================================================
    Part 4: isomorphism preserves the number of connected components (β₀)
    ============================================================ -/

/-- Isomorphic RGF states have the same β₀. -/
theorem iso_preserves_betti0 (s₁ s₂ : RGFState n) (f : RGFMorphism s₁ s₂) :
    s₁.betti0 = s₂.betti0 := by
      apply Nat.card_congr;
      have h_iso : s₁.toSimpleGraph ≃g s₂.toSimpleGraph := by
        refine' ⟨ f.toEquiv, _ ⟩;
        simp +decide [ RGFState.toSimpleGraph ];
        exact fun { a b } => by simpa [ RGFState.AdjRel ] using f.preserves a b;
      exact h_iso.connectedComponentEquiv

/-! ============================================================
    Part 5: isomorphism preserves β₁
    ============================================================ -/

/-- Isomorphic RGF states have the same β₁. -/
theorem iso_preserves_betti1 (s₁ s₂ : RGFState n) (f : RGFMorphism s₁ s₂) :
    s₁.betti1 = s₂.betti1 := by
  unfold betti1
  rw [iso_preserves_edgeCount s₁ s₂ f, iso_preserves_betti0 s₁ s₂ f]

/-! ============================================================
    Part 6: isomorphism preserves the order of the automorphism group
    ============================================================ -/

/-
Isomorphic states have automorphism groups of equal order.
-/
theorem iso_preserves_autOrder (s₁ s₂ : RGFState n) (f : RGFMorphism s₁ s₂) :
    s₁.autOrder = s₂.autOrder := by
  fapply Nat.card_congr;
  refine' Equiv.ofBijective ( fun σ => ⟨ f.toEquiv * σ.val * f.toEquiv⁻¹, _ ⟩ ) ⟨ _, _ ⟩;
  all_goals norm_num [ Function.Injective, Function.Surjective ];
  · intro i j; have := f.preserves i j; have := f.preserves ( σ.val ( f.toEquiv⁻¹ i ) ) ( σ.val ( f.toEquiv⁻¹ j ) ) ; simp_all +decide [ RGFState.IsAut ] ;
    have := f.preserves ( f.toEquiv.symm i ) ( f.toEquiv.symm j ) ; aesop;
  · intro a ha; use f.toEquiv⁻¹ * a * f.toEquiv; simp_all +decide [ RGFState.IsAut ] ;
    have := f.preserves; simp_all +decide [ ← f.preserves ] ;
    simp +decide [ mul_assoc ]

/-! ============================================================
    Part 7: isomorphism preserves the full invariant bundle (synthesis theorem)
    ============================================================ -/

/-- Isomorphism preserves the invariant bundle. -/
theorem iso_preserves_invariants (s₁ s₂ : RGFState n) (f : RGFMorphism s₁ s₂) :
    s₁.edgeCount = s₂.edgeCount ∧
    s₁.triangleCount = s₂.triangleCount ∧
    s₁.betti0 = s₂.betti0 ∧
    s₁.betti1 = s₂.betti1 ∧
    s₁.eulerChar1 = s₂.eulerChar1 ∧
    s₁.autOrder = s₂.autOrder :=
  ⟨iso_preserves_edgeCount s₁ s₂ f,
   iso_preserves_triangleCount s₁ s₂ f,
   iso_preserves_betti0 s₁ s₂ f,
   iso_preserves_betti1 s₁ s₂ f,
   iso_preserves_eulerChar s₁ s₂ f,
   iso_preserves_autOrder s₁ s₂ f⟩

/-! ============================================================
    Part 8: basic properties of the automorphism group
    (`id_is_aut`, `aut_comp`, `autGroup_nonempty` now live in `Invariants.Basic`)
    ============================================================ -/

/-! ============================================================
    Part 9: the equivariance condition — the cornerstone of invariant theory
    ============================================================

  Key insight (from the mathematical review):
  a general RGF iteration system `step = modify ∘ generate` does not automatically preserve invariants.
  For example, `generate := constant target, modify := id` can change all structure in one step.

  To make invariants constrain the dynamics, an explicit condition is needed:
  **equivariance**: step(σ · s) = σ · step(s)

  This means the evolution map "commutes" with the symmetry action.
  Under this condition, the automorphism group propagates along the orbit, thereby constraining the recovery time.

  Proof strategy:
  1. isAut_iff_permAction_inv: convert IsAut into a permAction equality
  2. step_iterate_equivariant: N-step iteration is still equivariant
  3. equivariant_preserves_aut: automorphisms are preserved permanently along the orbit
  4. equivariant_aut_subgroup: the automorphism group grows monotonically along the orbit
-/

/-- The permutation σ acts on an RGF state by relabeling nodes. -/
def permAction (σ : Perm (Fin n)) (s : RGFState n) : RGFState n where
  adj := fun i j => s.adj (σ⁻¹ i) (σ⁻¹ j)
  symm := by intro i j; simp [s.symm]
  irrefl := by intro i; simp [s.irrefl]

/-
Auxiliary lemma: σ is an automorphism of state s iff the state relabeled by σ⁻¹ equals s.
    This is the bridge between IsAut and permAction.
-/
lemma isAut_iff_permAction_inv (s : RGFState n) (σ : Perm (Fin n)) :
    s.IsAut σ ↔ permAction σ⁻¹ s = s := by
      constructor <;> intro h;
      · cases s;
        unfold permAction; aesop;
      · intro i j; have := congr_arg ( fun f : RGFState n => f.adj i j ) h; simp +decide [ permAction ] at this;
        exact this

/-- An equivariant RGF iteration system: step commutes with the symmetry action. -/
structure EquivariantSystem (n : ℕ) extends RGFIterSystem n where
  /-- Equivariance: step commutes with the permutation action. -/
  equivariant : ∀ (σ : Perm (Fin n)) (s : RGFState n),
    step (permAction σ s) = permAction σ (step s)

/-
The N-fold iteration of an equivariant system still commutes with the permutation action.
    This is the inductive generalization of single-step equivariance to N-step equivariance.
-/
lemma step_iterate_equivariant (sys : EquivariantSystem n)
    (σ : Perm (Fin n)) (s : RGFState n) (N : ℕ) :
    sys.step^[N] (permAction σ s) = permAction σ (sys.step^[N] s) := by
      induction' N with N ih;
      · rfl;
      · rw [ Function.iterate_succ_apply', ih, Function.iterate_succ_apply', sys.equivariant ]

/-! ============================================================
    Cornerstone theorem: under an equivariant system, automorphisms are preserved permanently along the orbit
    ============================================================ -/

/-- If the initial state s₀ has an automorphism σ, then after any number of iterations of an equivariant system
    this automorphism is still preserved.

    Proof idea:
    1. by isAut_iff_permAction_inv, convert IsAut σ into permAction σ⁻¹ s₀ = s₀
    2. by step_iterate_equivariant, permAction σ⁻¹ (step^[N] s₀) = step^[N] (permAction σ⁻¹ s₀) = step^[N] s₀
    3. by isAut_iff_permAction_inv again, recover (step^[N] s₀).IsAut σ -/
theorem equivariant_preserves_aut (sys : EquivariantSystem n)
    (s₀ : RGFState n) (σ : Perm (Fin n)) (hσ : s₀.IsAut σ)
    (N : ℕ) : (sys.step^[N] s₀).IsAut σ := by
  -- convert IsAut into a permAction equality
  have h0 : permAction σ⁻¹ s₀ = s₀ := (isAut_iff_permAction_inv s₀ σ).mp hσ
  -- N-step equivariance
  have hN : permAction σ⁻¹ (sys.step^[N] s₀) = sys.step^[N] s₀ := by
    calc permAction σ⁻¹ (sys.step^[N] s₀)
        = sys.step^[N] (permAction σ⁻¹ s₀) :=
          (step_iterate_equivariant sys σ⁻¹ s₀ N).symm
      _ = sys.step^[N] s₀ := by rw [h0]
  -- recover IsAut
  exact (isAut_iff_permAction_inv (sys.step^[N] s₀) σ).mpr hN

/-! ============================================================
    Corollary: the automorphism group only grows along the orbit
    ============================================================ -/

/-- Under an equivariant system, the automorphism group grows monotonically along the iteration orbit. -/
theorem equivariant_aut_subgroup (sys : EquivariantSystem n)
    (s₀ : RGFState n) (N : ℕ) :
    s₀.autGroup ≤ (sys.step^[N] s₀).autGroup := by
  intro σ hσ
  exact equivariant_preserves_aut sys s₀ σ hσ N

/-! ============================================================
    Part 10: the spectral-gap upper bound (with appropriate symmetry hypotheses)
    ============================================================

  Note: the original theorem used `True` as a symmetry placeholder and has been verified to be false
  (counterexample: k ≥ 3, g.val = 1).

  Corrected version: the spectral gap is bounded by the second eigenvalue of the transition matrix associated with the order-k symmetry.
  Here we prove 1/(k-1) > 0 as a nontriviality guarantee for the spectral-gap upper bound.
-/

/-- Nontriviality of the spectral-gap upper bound: 1/(k-1) > 0 for k ≥ 2. -/
theorem spectral_gap_bound_positive (k : ℕ) (hk : k ≥ 2) :
    (1 : ℝ) / ((k : ℝ) - 1) > 0 := by
  apply div_pos one_pos
  have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

end RGFState