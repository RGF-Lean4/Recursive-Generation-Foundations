import Mathlib

/-!
# Order of the type-B₃ Coxeter group

We prove `Nat.card (CoxeterMatrix.Bₙ 3).Group = 48` and hence that `W_B3` has no
element of order `5`, via the same covering-finset + complete-rewriting-system
method used for A₃.  The Coxeter diagram of B₃ is `0 —3— 1 —4— 2`.
-/

namespace RGF.CoxeterOrderB3

open CoxeterMatrix CoxeterSystem
open scoped Classical

abbrev W_B3 := (CoxeterMatrix.Bₙ 3).Group
noncomputable def cs : CoxeterSystem (CoxeterMatrix.Bₙ 3) W_B3 := (CoxeterMatrix.Bₙ 3).toCoxeterSystem
noncomputable abbrev s (i : Fin 3) : W_B3 := cs.simple i

/-! ### The Coxeter relations of B₃ -/

lemma sinv (i : Fin 3) : s i * s i = 1 := by simp [s]
lemma sinv' (i : Fin 3) : (s i)⁻¹ = s i := inv_eq_of_mul_eq_one_right (sinv i)
lemma braidgen (i j : Fin 3) (n : ℕ) (h : (CoxeterMatrix.Bₙ 3).M i j = n) :
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
lemma b2 : s 1 * s 2 * s 1 * s 2 = s 2 * s 1 * s 2 * s 1 := by
  have h : (s 1 * s 2) ^ 4 = 1 := braidgen 1 2 4 (by decide)
  have hexp : (s 1 * s 2) ^ 4 = (s 1*s 2*s 1*s 2)*(s 1*s 2*s 1*s 2) := by
    simp only [pow_succ, pow_zero, one_mul]; group
  rw [hexp] at h; have := eq_inv_of_mul_eq_one_left h; rw [this]; simp [mul_inv_rev, mul_assoc]

/-! ### Complete rewriting system for B₃ (tail form) -/

lemma r_inv (i : Fin 3) (x : W_B3) : s i * (s i * x) = x := by rw [← mul_assoc, sinv, one_mul]
lemma r02 (x : W_B3) : s 0 * (s 2 * x) = s 2 * (s 0 * x) := by rw [← mul_assoc, comm02, mul_assoc]
lemma r101 (x : W_B3) : s 1 * (s 0 * (s 1 * x)) = s 0 * (s 1 * (s 0 * x)) := by
  rw [← mul_assoc, ← mul_assoc, ← braid01, mul_assoc, mul_assoc]
lemma r_b2 (x : W_B3) : s 1 * (s 2 * (s 1 * (s 2 * x))) = s 2 * (s 1 * (s 2 * (s 1 * x))) := by
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, b2, mul_assoc, mul_assoc, mul_assoc]
lemma big_flat : s 0*s 1*s 2*s 0*s 1*s 2 = s 1*s 2*s 0*s 1*s 2*s 1 := by
  calc s 0*s 1*s 2*s 0*s 1*s 2
      = s 0*s 1*(s 2*s 0)*s 1*s 2 := by group
    _ = s 0*s 1*(s 0*s 2)*s 1*s 2 := by rw [comm02]
    _ = (s 0*s 1*s 0)*s 2*s 1*s 2 := by group
    _ = (s 1*s 0*s 1)*s 2*s 1*s 2 := by rw [braid01]
    _ = s 1*s 0*(s 1*s 2*s 1*s 2) := by group
    _ = s 1*s 0*(s 2*s 1*s 2*s 1) := by rw [b2]
    _ = s 1*(s 0*s 2)*s 1*s 2*s 1 := by group
    _ = s 1*(s 2*s 0)*s 1*s 2*s 1 := by rw [comm02]
    _ = s 1*s 2*s 0*s 1*s 2*s 1 := by group
lemma r_big (x : W_B3) :
    s 0*(s 1*(s 2*(s 0*(s 1*(s 2* x))))) = s 1*(s 2*(s 0*(s 1*(s 2*(s 1* x))))) := by
  calc s 0*(s 1*(s 2*(s 0*(s 1*(s 2* x)))))
      = (s 0*s 1*s 2*s 0*s 1*s 2)*x := by group
    _ = (s 1*s 2*s 0*s 1*s 2*s 1)*x := by rw [big_flat]
    _ = s 1*(s 2*(s 0*(s 1*(s 2*(s 1* x))))) := by group

/-! ### The covering finset -/

/-- The 48 reduced words enumerating all elements of `W_B3`. -/
def Lwords : List (List (Fin 3)) :=
  [[], [0], [1], [2], [1,0], [2,0], [0,1], [2,1], [1,2], [0,1,0], [2,1,0], [1,2,0],
   [2,0,1], [1,2,1], [0,1,2], [2,1,2], [2,0,1,0], [1,2,1,0], [0,1,2,0], [2,1,2,0],
   [1,2,0,1], [0,1,2,1], [2,1,2,1], [2,0,1,2], [1,2,0,1,0], [0,1,2,1,0], [2,1,2,1,0],
   [2,0,1,2,0], [0,1,2,0,1], [2,1,2,0,1], [2,0,1,2,1], [1,2,0,1,2], [0,1,2,0,1,0],
   [2,1,2,0,1,0], [2,0,1,2,1,0], [1,2,0,1,2,0], [2,0,1,2,0,1], [1,2,0,1,2,1],
   [2,1,2,0,1,2], [2,0,1,2,0,1,0], [1,2,0,1,2,1,0], [2,1,2,0,1,2,0], [1,2,0,1,2,0,1],
   [2,1,2,0,1,2,1], [1,2,0,1,2,0,1,0], [2,1,2,0,1,2,1,0], [2,1,2,0,1,2,0,1],
   [2,1,2,0,1,2,0,1,0]]

/-- The covering finset. -/
noncomputable def T : Finset W_B3 := (Lwords.map cs.wordProd).toFinset

lemma mem_T_of (v : List (Fin 3)) (hv : v ∈ Lwords) (y : W_B3) (h : y = cs.wordProd v) : y ∈ T := by
  simp only [T, List.mem_toFinset, List.mem_map]; exact ⟨v, hv, h.symm⟩

macro "normW" : tactic =>
  `(tactic| (simp only [cs.wordProd_cons, cs.wordProd_nil, r_inv, r02, r101, r_b2, r_big]; done))

lemma T_closed0 (w : List (Fin 3)) (hw : w ∈ Lwords) : cs.simple 0 * cs.wordProd w ∈ T := by
  simp only [Lwords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rw [← cs.wordProd_cons]
  · exact mem_T_of [0] (by decide) _ (by normW)
  · exact mem_T_of [] (by decide) _ (by normW)
  · exact mem_T_of [0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2] (by decide) _ (by normW)
  · exact mem_T_of [1] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,0,1] (by decide) _ (by normW)
lemma T_closed1 (w : List (Fin 3)) (hw : w ∈ Lwords) : cs.simple 1 * cs.wordProd w ∈ T := by
  simp only [Lwords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rw [← cs.wordProd_cons]
  · exact mem_T_of [1] (by decide) _ (by normW)
  · exact mem_T_of [1,0] (by decide) _ (by normW)
  · exact mem_T_of [] (by decide) _ (by normW)
  · exact mem_T_of [1,2] (by decide) _ (by normW)
  · exact mem_T_of [0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2] (by decide) _ (by normW)
  · exact mem_T_of [0,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,1,0] (by decide) _ (by normW)
lemma T_closed2 (w : List (Fin 3)) (hw : w ∈ Lwords) : cs.simple 2 * cs.wordProd w ∈ T := by
  simp only [Lwords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rw [← cs.wordProd_cons]
  · exact mem_T_of [2] (by decide) _ (by normW)
  · exact mem_T_of [2,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1] (by decide) _ (by normW)
  · exact mem_T_of [] (by decide) _ (by normW)
  · exact mem_T_of [2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [2,0,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2] (by decide) _ (by normW)
  · exact mem_T_of [0,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,0] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,1] (by decide) _ (by normW)
  · exact mem_T_of [2,1,2,0,1,2,0,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,1,0] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,0,1] (by decide) _ (by normW)
  · exact mem_T_of [1,2,0,1,2,0,1,0] (by decide) _ (by normW)
lemma T_closed_mem (i : Fin 3) (x : W_B3) (hx : x ∈ T) : cs.simple i * x ∈ T := by
  simp only [T, List.mem_toFinset, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  fin_cases i
  · exact T_closed0 w hw
  · exact T_closed1 w hw
  · exact T_closed2 w hw

lemma one_mem_T : (1 : W_B3) ∈ T := by
  simp only [T, List.mem_toFinset, List.mem_map]
  exact ⟨[], by simp [Lwords], by simp [cs.wordProd_nil]⟩

lemma wordProd_mem_T : ∀ l : List (Fin 3), cs.wordProd l ∈ T := by
  intro l
  induction l with
  | nil => simpa [cs.wordProd_nil] using one_mem_T
  | cons i l ih => rw [cs.wordProd_cons]; exact T_closed_mem i _ ih

lemma all_mem_T (x : W_B3) : x ∈ T := by
  obtain ⟨l, _, rfl⟩ := cs.exists_reduced_word x
  exact wordProd_mem_T l

instance B3_finite : Finite W_B3 := by
  have hsub : (Set.univ : Set W_B3) ⊆ (↑T : Set W_B3) := fun x _ => all_mem_T x
  exact Set.finite_univ_iff.mp (Set.Finite.subset T.finite_toSet hsub)

lemma card_B3_le : Nat.card W_B3 ≤ 48 := by
  have huniv : (Set.univ : Set W_B3) = (↑T : Set W_B3) :=
    Set.Subset.antisymm (fun x _ => all_mem_T x) (Set.subset_univ _)
  have h1 : Nat.card W_B3 = T.card := by
    rw [← Set.ncard_univ, huniv, Set.ncard_coe_finset]
  rw [h1]
  calc T.card ≤ (Lwords.map cs.wordProd).length := List.toFinset_card_le _
    _ = Lwords.length := by rw [List.length_map]
    _ = 48 := by simp [Lwords]

/-! ### Faithful signed-permutation representation for the lower bound -/

/-- B₃ acts by signed permutations of `{±e₀, ±e₁, ±e₂}`, modelled on `Fin 6`
(`0,1,2 = +e₀,+e₁,+e₂`; `3,4,5 = -e₀,-e₁,-e₂`). -/
def repB3 : Fin 3 → Equiv.Perm (Fin 6)
  | 0 => Equiv.swap 0 1 * Equiv.swap 3 4
  | 1 => Equiv.swap 1 2 * Equiv.swap 4 5
  | 2 => Equiv.swap 2 5

theorem hliftB3 : IsLiftable (CoxeterMatrix.Bₙ 3) repB3 := by
  intro i i'; fin_cases i <;> fin_cases i' <;> decide

noncomputable def rhoB3 : W_B3 →* Equiv.Perm (Fin 6) := cs.lift ⟨repB3, hliftB3⟩

lemma rhoB3_wordProd (w : List (Fin 3)) : rhoB3 (cs.wordProd w) = (w.map repB3).prod := by
  induction w with
  | nil => simp [cs.wordProd_nil, rhoB3]
  | cons i l ih =>
      rw [cs.wordProd_cons, map_mul, List.map_cons, List.prod_cons, ih, rhoB3,
        CoxeterSystem.lift_apply_simple]

/-- The 48 covering words have pairwise-distinct images, so the covering finset has
exactly 48 elements. -/
lemma T_card : T.card = 48 := by
  have hnodup : (Lwords.map cs.wordProd).Nodup := by
    apply List.Nodup.of_map rhoB3
    rw [List.map_map]
    have : (Lwords.map (rhoB3 ∘ cs.wordProd)) = Lwords.map (fun w => (w.map repB3).prod) := by
      apply List.map_congr_left; intro w _; simp [Function.comp, rhoB3_wordProd]
    rw [this]; native_decide
  rw [T, List.toFinset_card_of_nodup hnodup, List.length_map]; simp [Lwords]

/-- The type-B₃ Coxeter group has exactly 48 elements. -/
theorem card_B3 : Nat.card W_B3 = 48 := by
  have huniv : (Set.univ : Set W_B3) = (↑T : Set W_B3) :=
    Set.Subset.antisymm (fun x _ => all_mem_T x) (Set.subset_univ _)
  rw [← Set.ncard_univ, huniv, Set.ncard_coe_finset, T_card]

/-- B₃ (order 48) has no element of order 5. -/
theorem W_B3_no_order5 (g : W_B3) : orderOf g ≠ 5 := by
  intro h
  have hdvd : orderOf g ∣ Nat.card W_B3 := orderOf_dvd_natCard g
  rw [h, card_B3] at hdvd
  norm_num at hdvd

end RGF.CoxeterOrderB3
