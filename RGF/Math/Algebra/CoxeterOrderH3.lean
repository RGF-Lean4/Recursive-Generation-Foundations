import Mathlib

/-!
# Order of the non-crystallographic Coxeter group H₃

We prove `Nat.card (CoxeterMatrix.H₃).Group = 120` and hence that `W_H3` has no
element of order dividing incorrectly... (it *does* contain order-5 elements).

Method (identical to the A₃/B₃ development): a `120`-element covering finset `T`
of reduced words, shown closed under left multiplication by the simple reflections
via a **complete rewriting system** for H₃ (Coxeter diagram `0 —3— 1 —5— 2`),
computed by Knuth–Bendix.  This forces `W_H3` finite with `Nat.card ≤ 120`; a
faithful `3×3` matrix representation over `𝔽₁₁` (which has order exactly `120`)
supplies the matching lower bound.

The complete rewriting system (shortlex, `0<1<2`) has 9 rules:
`aa,bb,cc → ε`, `ca → ac`, `bab → aba`, `cbcbc → bcbcb`, `cbcbac → bcbcba`,
`cbacbacbcb → bcbacbacbc`, `cbacbacbacba → bcbacbacbacb`.
-/

namespace RGF.CoxeterOrderH3

open CoxeterMatrix CoxeterSystem
open scoped Classical

abbrev W_H3 := (CoxeterMatrix.H₃).Group
noncomputable def cs : CoxeterSystem CoxeterMatrix.H₃ W_H3 := CoxeterMatrix.H₃.toCoxeterSystem
noncomputable abbrev s (i : Fin 3) : W_H3 := cs.simple i

/-! ### The Coxeter relations of H₃ (diagram `0 —3— 1 —5— 2`) -/

lemma sinv (i : Fin 3) : s i * s i = 1 := cs.simple_mul_simple_self i
lemma braidgen (i j : Fin 3) (n : ℕ) (h : (CoxeterMatrix.H₃).M i j = n) :
    (s i * s j) ^ n = 1 := by
  have := cs.simple_mul_simple_pow i j; rw [h] at this; simpa [s] using this

lemma comm02 : s 0 * s 2 = s 2 * s 0 := by
  have h : (s 0 * s 2) ^ 2 = 1 := braidgen 0 2 2 (by decide)
  rw [pow_two] at h; have := eq_inv_of_mul_eq_one_left h; rw [this]; simp [mul_inv_rev]
lemma braid01 : s 0 * s 1 * s 0 = s 1 * s 0 * s 1 := by
  have h : (s 0 * s 1) ^ 3 = 1 := braidgen 0 1 3 (by decide)
  have hexp : (s 0 * s 1) ^ 3 = (s 0*s 1*s 0)*(s 1*s 0*s 1) := by
    simp only [pow_succ, pow_zero, one_mul]; group
  rw [hexp] at h; have := eq_inv_of_mul_eq_one_left h; rw [this]; simp [mul_inv_rev, mul_assoc]
lemma braid12 : s 1 * s 2 * s 1 * s 2 * s 1 = s 2 * s 1 * s 2 * s 1 * s 2 := by
  have h : (s 1 * s 2) ^ 5 = 1 := braidgen 1 2 5 (by decide)
  have hexp : (s 1 * s 2) ^ 5 = (s 1*s 2*s 1*s 2*s 1)*(s 2*s 1*s 2*s 1*s 2) := by
    simp only [pow_succ, pow_zero, one_mul]; group
  rw [hexp] at h; have := eq_inv_of_mul_eq_one_left h
  rw [this]; simp [mul_inv_rev, mul_assoc]

/-! ### Complete rewriting system for H₃ (tail form).  All rules are shortlex
decreasing, hence `simp` with them terminates and (by Knuth–Bendix confluence)
normalises every word. -/

lemma r_inv (i : Fin 3) (x : W_H3) : s i * (s i * x) = x := by rw [← mul_assoc, sinv, one_mul]
lemma r_ca (x : W_H3) : s 2 * (s 0 * x) = s 0 * (s 2 * x) := by
  rw [← mul_assoc, ← comm02, mul_assoc]
lemma r_bab (x : W_H3) : s 1 * (s 0 * (s 1 * x)) = s 0 * (s 1 * (s 0 * x)) := by
  rw [← mul_assoc, ← mul_assoc, ← braid01, mul_assoc, mul_assoc]
lemma r_cbcbc (x : W_H3) :
    s 2*(s 1*(s 2*(s 1*(s 2* x)))) = s 1*(s 2*(s 1*(s 2*(s 1* x)))) := by
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← braid12,
    mul_assoc, mul_assoc, mul_assoc, mul_assoc]


/-- Derived rewriting rule `cbcbac → bcbcba`.  Consequence of the braid relations;
proved by the theorem-proving subagent. -/
lemma r_cbcbac (x : W_H3) :
    s 2*(s 1*(s 2*(s 1*(s 0*(s 2* x))))) = s 1*(s 2*(s 1*(s 2*(s 1*(s 0* x))))) := by
  rw [← r_ca x, r_cbcbc (s 0 * x)]

/-
Derived rewriting rule `cbacbacbcb → bcbacbacbc`.
-/
lemma r_long1 (x : W_H3) :
    s 2*(s 1*(s 0*(s 2*(s 1*(s 0*(s 2*(s 1*(s 2*(s 1* x))))))))) =
      s 1*(s 2*(s 1*(s 0*(s 2*(s 1*(s 0*(s 2*(s 1*(s 2* x))))))))) := by
  grind +suggestions

/-
Derived rewriting rule `cbacbacbacba → bcbacbacbacb`.
-/
lemma r_long2 (x : W_H3) :
    s 2*(s 1*(s 0*(s 2*(s 1*(s 0*(s 2*(s 1*(s 0*(s 2*(s 1*(s 0* x))))))))))) =
      s 1*(s 2*(s 1*(s 0*(s 2*(s 1*(s 0*(s 2*(s 1*(s 0*(s 2*(s 1* x))))))))))) := by
  grind +suggestions

/-- The 120 reduced words enumerating all elements of `W_H3`. -/
def Lwords : List (List (Fin 3)) :=
  [[], [0], [1], [2], [0,1], [0,2], [1,0], [1,2],
   [2,1], [0,1,0], [0,1,2], [0,2,1], [1,0,2], [1,2,1], [2,1,0], [2,1,2],
   [0,1,0,2], [0,1,2,1], [0,2,1,0], [0,2,1,2], [1,0,2,1], [1,2,1,0], [1,2,1,2], [2,1,0,2],
   [2,1,2,1], [0,1,0,2,1], [0,1,2,1,0], [0,1,2,1,2], [0,2,1,0,2], [0,2,1,2,1], [1,0,2,1,0], [1,0,2,1,2],
   [1,2,1,0,2], [1,2,1,2,1], [2,1,0,2,1], [2,1,2,1,0], [0,1,0,2,1,0], [0,1,0,2,1,2], [0,1,2,1,0,2], [0,1,2,1,2,1],
   [0,2,1,0,2,1], [0,2,1,2,1,0], [1,0,2,1,0,2], [1,0,2,1,2,1], [1,2,1,0,2,1], [1,2,1,2,1,0], [2,1,0,2,1,0], [2,1,0,2,1,2],
   [0,1,0,2,1,0,2], [0,1,0,2,1,2,1], [0,1,2,1,0,2,1], [0,1,2,1,2,1,0], [0,2,1,0,2,1,0], [0,2,1,0,2,1,2], [1,0,2,1,0,2,1], [1,0,2,1,2,1,0],
   [1,2,1,0,2,1,0], [1,2,1,0,2,1,2], [2,1,0,2,1,0,2], [2,1,0,2,1,2,1], [0,1,0,2,1,0,2,1], [0,1,0,2,1,2,1,0], [0,1,2,1,0,2,1,0], [0,1,2,1,0,2,1,2],
   [0,2,1,0,2,1,0,2], [0,2,1,0,2,1,2,1], [1,0,2,1,0,2,1,0], [1,0,2,1,0,2,1,2], [1,2,1,0,2,1,0,2], [1,2,1,0,2,1,2,1], [2,1,0,2,1,0,2,1], [2,1,0,2,1,2,1,0],
   [0,1,0,2,1,0,2,1,0], [0,1,0,2,1,0,2,1,2], [0,1,2,1,0,2,1,0,2], [0,1,2,1,0,2,1,2,1], [0,2,1,0,2,1,0,2,1], [0,2,1,0,2,1,2,1,0], [1,0,2,1,0,2,1,0,2], [1,0,2,1,0,2,1,2,1],
   [1,2,1,0,2,1,0,2,1], [1,2,1,0,2,1,2,1,0], [2,1,0,2,1,0,2,1,0], [2,1,0,2,1,0,2,1,2], [0,1,0,2,1,0,2,1,0,2], [0,1,0,2,1,0,2,1,2,1], [0,1,2,1,0,2,1,0,2,1], [0,1,2,1,0,2,1,2,1,0],
   [0,2,1,0,2,1,0,2,1,0], [0,2,1,0,2,1,0,2,1,2], [1,0,2,1,0,2,1,0,2,1], [1,0,2,1,0,2,1,2,1,0], [1,2,1,0,2,1,0,2,1,0], [1,2,1,0,2,1,0,2,1,2], [2,1,0,2,1,0,2,1,0,2], [0,1,0,2,1,0,2,1,0,2,1],
   [0,1,0,2,1,0,2,1,2,1,0], [0,1,2,1,0,2,1,0,2,1,0], [0,1,2,1,0,2,1,0,2,1,2], [0,2,1,0,2,1,0,2,1,0,2], [1,0,2,1,0,2,1,0,2,1,0], [1,0,2,1,0,2,1,0,2,1,2], [1,2,1,0,2,1,0,2,1,0,2], [2,1,0,2,1,0,2,1,0,2,1],
   [0,1,0,2,1,0,2,1,0,2,1,0], [0,1,0,2,1,0,2,1,0,2,1,2], [0,1,2,1,0,2,1,0,2,1,0,2], [0,2,1,0,2,1,0,2,1,0,2,1], [1,0,2,1,0,2,1,0,2,1,0,2], [1,2,1,0,2,1,0,2,1,0,2,1], [2,1,0,2,1,0,2,1,0,2,1,2], [0,1,0,2,1,0,2,1,0,2,1,0,2],
   [0,1,2,1,0,2,1,0,2,1,0,2,1], [0,2,1,0,2,1,0,2,1,0,2,1,2], [1,0,2,1,0,2,1,0,2,1,0,2,1], [1,2,1,0,2,1,0,2,1,0,2,1,2], [0,1,0,2,1,0,2,1,0,2,1,0,2,1], [0,1,2,1,0,2,1,0,2,1,0,2,1,2], [1,0,2,1,0,2,1,0,2,1,0,2,1,2], [0,1,0,2,1,0,2,1,0,2,1,0,2,1,2]]

/-- The covering finset. -/
noncomputable def T : Finset W_H3 := (Lwords.map cs.wordProd).toFinset

lemma mem_T_of (v : List (Fin 3)) (hv : v ∈ Lwords) (y : W_H3) (h : y = cs.wordProd v) : y ∈ T := by
  simp only [T, List.mem_toFinset, List.mem_map]; exact ⟨v, hv, h.symm⟩

macro "normW" : tactic =>
  `(tactic| (simp only [cs.wordProd_cons, cs.wordProd_nil, r_inv, r_ca, r_bab, r_cbcbc,
      r_cbcbac, r_long1, r_long2]; done))

lemma T_closed0 (w : List (Fin 3)) (hw : w ∈ Lwords) : cs.simple 0 * cs.wordProd w ∈ T := by
  simp only [Lwords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rw [← cs.wordProd_cons]
  · exact mem_T_of [0] (by decide) _ (by normW)
  · exact mem_T_of [] (by decide) _ (by normW)
  · exact mem_T_of [0,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2] (by decide) _ (by normW)
  · exact mem_T_of [1] (by decide) _ (by normW)
  · exact mem_T_of [2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
lemma T_closed1 (w : List (Fin 3)) (hw : w ∈ Lwords) : cs.simple 1 * cs.wordProd w ∈ T := by
  simp only [Lwords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rw [← cs.wordProd_cons]
  · exact mem_T_of [1] (by decide) _ (by normW)
  · exact mem_T_of [1,0] (by decide) _ (by normW)
  · exact mem_T_of [] (by decide) _ (by normW)
  · exact mem_T_of [1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0] (by decide) _ (by normW)
  · exact mem_T_of [2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
lemma T_closed2 (w : List (Fin 3)) (hw : w ∈ Lwords) : cs.simple 2 * cs.wordProd w ∈ T := by
  simp only [Lwords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rw [← cs.wordProd_cons]
  · exact mem_T_of [2] (by decide) _ (by normW)
  · exact mem_T_of [0,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1] (by decide) _ (by normW)
  · exact mem_T_of [] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0,2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0,2,1,0,2,1,0,2,1,0,2,1] (by decide) _ (by normW)
lemma T_closed_mem (i : Fin 3) (x : W_H3) (hx : x ∈ T) : cs.simple i * x ∈ T := by
  simp only [T, List.mem_toFinset, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  fin_cases i
  · exact T_closed0 w hw
  · exact T_closed1 w hw
  · exact T_closed2 w hw

lemma one_mem_T : (1 : W_H3) ∈ T := by
  simp only [T, List.mem_toFinset, List.mem_map]
  exact ⟨[], by simp [Lwords], by simp [cs.wordProd_nil]⟩

lemma wordProd_mem_T : ∀ l : List (Fin 3), cs.wordProd l ∈ T := by
  intro l
  induction l with
  | nil => simpa [cs.wordProd_nil] using one_mem_T
  | cons i l ih => rw [cs.wordProd_cons]; exact T_closed_mem i _ ih

lemma all_mem_T (x : W_H3) : x ∈ T := by
  obtain ⟨l, _, rfl⟩ := cs.exists_reduced_word x
  exact wordProd_mem_T l

instance H3_finite : Finite W_H3 := by
  have hsub : (Set.univ : Set W_H3) ⊆ (↑T : Set W_H3) := fun x _ => all_mem_T x
  exact Set.finite_univ_iff.mp (Set.Finite.subset T.finite_toSet hsub)

/-! ### Faithful permutation representation for the lower bound.
H₃ (the icosahedral group `A₅ × C₂`) acts faithfully on a `12`-point set (obtained
as the union of small orbits of the faithful `𝔽₁₁` reflection representation on
`𝔽₁₁³`).  Using permutations of `Fin 12` (rather than matrices) keeps the
`native_decide` distinctness check fast.  The three involutions are:
`s₀ = (0 7)(1 8)(4 6)(5 9)`, `s₁ = (0 2)(3 4)(8 11)(9 10)`,
`s₂ = (0 1)(2 3)(7 8)(10 11)`. -/

def repH3 : Fin 3 → Equiv.Perm (Fin 12) :=
  ![ Equiv.swap 0 7 * Equiv.swap 1 8 * Equiv.swap 4 6 * Equiv.swap 5 9,
     Equiv.swap 0 2 * Equiv.swap 3 4 * Equiv.swap 8 11 * Equiv.swap 9 10,
     Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 7 8 * Equiv.swap 10 11 ]

set_option maxRecDepth 10000 in
theorem hliftH3 : IsLiftable CoxeterMatrix.H₃ repH3 := by
  intro i i'; fin_cases i <;> fin_cases i' <;> decide

noncomputable def rhoH3 : W_H3 →* Equiv.Perm (Fin 12) := cs.lift ⟨repH3, hliftH3⟩

lemma rhoH3_wordProd (w : List (Fin 3)) : rhoH3 (cs.wordProd w) = (w.map repH3).prod := by
  induction w with
  | nil => simp [cs.wordProd_nil, rhoH3]
  | cons i l ih =>
      rw [cs.wordProd_cons, map_mul, List.map_cons, List.prod_cons, ih, rhoH3,
        CoxeterSystem.lift_apply_simple]

/-- The 120 covering words have pairwise-distinct images, so `T` has exactly 120
elements. -/
lemma T_card : T.card = 120 := by
  have hnodup : (Lwords.map cs.wordProd).Nodup := by
    apply List.Nodup.of_map rhoH3
    rw [List.map_map]
    have : (Lwords.map (rhoH3 ∘ cs.wordProd)) = Lwords.map (fun w => (w.map repH3).prod) := by
      apply List.map_congr_left; intro w _; simp [Function.comp, rhoH3_wordProd]
    rw [this]; native_decide
  rw [T, List.toFinset_card_of_nodup hnodup, List.length_map]; simp [Lwords]

/-- The non-crystallographic Coxeter group H₃ has exactly 120 elements. -/
theorem card_H3 : Nat.card W_H3 = 120 := by
  have huniv : (Set.univ : Set W_H3) = (↑T : Set W_H3) :=
    Set.Subset.antisymm (fun x _ => all_mem_T x) (Set.subset_univ _)
  rw [← Set.ncard_univ, huniv, Set.ncard_coe_finset, T_card]

end RGF.CoxeterOrderH3