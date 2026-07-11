import Mathlib

/-!
# Order of the type-A₃ Coxeter group

We prove that the abstract type-A₃ Coxeter group `(CoxeterMatrix.Aₙ 3).Group`
has exactly `24` elements and hence (being of order `24`, coprime to `5`) contains
no element of order `5`.

The strategy avoids the (Mathlib-absent) classification of finite Coxeter groups:

* An explicit 24-element finset `T` of reduced words is shown to be closed under
  left multiplication by the simple reflections, via a *complete rewriting system*
  for `S₄` (`r_inv`, `r02`, `r101`, `r212`, `r2012`). Since the simple reflections
  generate the group and every element is a `wordProd`, this forces `T` to be all
  of the group, giving `Finite` and `Nat.card ≤ 24`.
* The reflection representation into `Perm (Fin 4)` (adjacent transpositions) is
  surjective, giving `Nat.card ≥ 24`.

Hence `Nat.card = 24`.
-/

namespace RGF.CoxeterOrdersExp

open CoxeterMatrix CoxeterSystem Equiv
open scoped Classical

abbrev W_A3 := (CoxeterMatrix.Aₙ 3).Group
noncomputable def cs : CoxeterSystem (CoxeterMatrix.Aₙ 3) W_A3 := (CoxeterMatrix.Aₙ 3).toCoxeterSystem

/-! ### The Coxeter relations of A₃ -/

lemma sinv (i : Fin 3) : cs.simple i * cs.simple i = 1 := by
  simp
lemma braidgen (i j : Fin 3) (n : ℕ) (h : (CoxeterMatrix.Aₙ 3).M i j = n) :
    (cs.simple i * cs.simple j) ^ n = 1 := by
  have := cs.simple_mul_simple_pow i j; rw [h] at this; simpa using this
lemma braid01 : cs.simple 0 * cs.simple 1 * cs.simple 0 = cs.simple 1 * cs.simple 0 * cs.simple 1 := by
  have h : (cs.simple 0 * cs.simple 1) ^ 3 = 1 := braidgen 0 1 3 (by decide)
  have hexp : (cs.simple 0 * cs.simple 1) ^ 3
      = (cs.simple 0 * cs.simple 1 * cs.simple 0) * (cs.simple 1 * cs.simple 0 * cs.simple 1) := by
    simp only [pow_succ, pow_zero, one_mul]; group
  rw [hexp] at h; have := eq_inv_of_mul_eq_one_left h; rw [this]; simp [mul_inv_rev, mul_assoc]
lemma braid12 : cs.simple 1 * cs.simple 2 * cs.simple 1 = cs.simple 2 * cs.simple 1 * cs.simple 2 := by
  have h : (cs.simple 1 * cs.simple 2) ^ 3 = 1 := braidgen 1 2 3 (by decide)
  have hexp : (cs.simple 1 * cs.simple 2) ^ 3
      = (cs.simple 1 * cs.simple 2 * cs.simple 1) * (cs.simple 2 * cs.simple 1 * cs.simple 2) := by
    simp only [pow_succ, pow_zero, one_mul]; group
  rw [hexp] at h; have := eq_inv_of_mul_eq_one_left h; rw [this]; simp [mul_inv_rev, mul_assoc]
lemma comm02 : cs.simple 0 * cs.simple 2 = cs.simple 2 * cs.simple 0 := by
  have h : (cs.simple 0 * cs.simple 2) ^ 2 = 1 := braidgen 0 2 2 (by decide)
  rw [pow_two] at h; have := eq_inv_of_mul_eq_one_left h; rw [this]; simp [mul_inv_rev]

/-! ### Complete rewriting system for S₄ (tail form) -/

lemma r_inv (i : Fin 3) (x : W_A3) : cs.simple i * (cs.simple i * x) = x := by
  rw [← mul_assoc, sinv, one_mul]
lemma r02 (x : W_A3) : cs.simple 0 * (cs.simple 2 * x) = cs.simple 2 * (cs.simple 0 * x) := by
  rw [← mul_assoc, comm02, mul_assoc]
lemma r101 (x : W_A3) :
    cs.simple 1 * (cs.simple 0 * (cs.simple 1 * x)) = cs.simple 0 * (cs.simple 1 * (cs.simple 0 * x)) := by
  rw [← mul_assoc, ← mul_assoc, ← braid01, mul_assoc, mul_assoc]
lemma r212 (x : W_A3) :
    cs.simple 2 * (cs.simple 1 * (cs.simple 2 * x)) = cs.simple 1 * (cs.simple 2 * (cs.simple 1 * x)) := by
  rw [← mul_assoc, ← mul_assoc, ← braid12, mul_assoc, mul_assoc]
lemma r2012 (x : W_A3) :
    cs.simple 2 * (cs.simple 0 * (cs.simple 1 * (cs.simple 2 * x)))
      = cs.simple 0 * (cs.simple 1 * (cs.simple 2 * (cs.simple 1 * x))) := by
  rw [← mul_assoc, ← comm02, mul_assoc, r212]

/-! ### The covering finset -/

/-- The 24 reduced words (alphabet `Fin 3`) enumerating all elements of `W_A3`. -/
def Lwords : List (List (Fin 3)) :=
  [[], [0], [1], [2], [1,0], [2,0], [0,1], [2,1], [1,2], [0,1,0], [2,1,0], [1,2,0],
   [2,0,1], [1,2,1], [0,1,2], [2,0,1,0], [1,2,1,0], [0,1,2,0], [1,2,0,1], [0,1,2,1],
   [1,2,0,1,0], [0,1,2,1,0], [0,1,2,0,1], [0,1,2,0,1,0]]

/-- The covering finset: images of the 24 words under `wordProd`. -/
noncomputable def T : Finset W_A3 := (Lwords.map cs.wordProd).toFinset

lemma mem_T_of (v : List (Fin 3)) (hv : v ∈ Lwords) (y : W_A3) (h : y = cs.wordProd v) : y ∈ T := by
  simp only [T, List.mem_toFinset, List.mem_map]; exact ⟨v, hv, h.symm⟩

/-- Try to realise the current membership goal by the reduced word `v`, normalising
the word product with the rewriting system. -/
macro "tryV" v:term : tactic =>
  `(tactic| (refine mem_T_of $v (by decide) _ ?_;
             simp only [cs.wordProd_cons, cs.wordProd_nil, r_inv, r02, r101, r212, r2012]; done))

/-- Search over the 24 reduced words for the one that closes the membership goal. -/
macro "closeW" : tactic => `(tactic|
  first
  | tryV [] | tryV [0] | tryV [1] | tryV [2] | tryV [1,0] | tryV [2,0] | tryV [0,1] | tryV [2,1]
  | tryV [1,2] | tryV [0,1,0] | tryV [2,1,0] | tryV [1,2,0] | tryV [2,0,1] | tryV [1,2,1] | tryV [0,1,2]
  | tryV [2,0,1,0] | tryV [1,2,1,0] | tryV [0,1,2,0] | tryV [1,2,0,1] | tryV [0,1,2,1]
  | tryV [1,2,0,1,0] | tryV [0,1,2,1,0] | tryV [0,1,2,0,1] | tryV [0,1,2,0,1,0])

lemma T_closed0 (w : List (Fin 3)) (hw : w ∈ Lwords) : cs.simple 0 * cs.wordProd w ∈ T := by
  simp only [Lwords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rw [← cs.wordProd_cons] <;> closeW
lemma T_closed1 (w : List (Fin 3)) (hw : w ∈ Lwords) : cs.simple 1 * cs.wordProd w ∈ T := by
  simp only [Lwords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rw [← cs.wordProd_cons] <;> closeW
lemma T_closed2 (w : List (Fin 3)) (hw : w ∈ Lwords) : cs.simple 2 * cs.wordProd w ∈ T := by
  simp only [Lwords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rw [← cs.wordProd_cons] <;> closeW

/-- Closure of the covering finset under left multiplication by simple reflections. -/
lemma T_closed (i : Fin 3) (w : List (Fin 3)) (hw : w ∈ Lwords) :
    cs.simple i * cs.wordProd w ∈ T := by
  fin_cases i
  · exact T_closed0 w hw
  · exact T_closed1 w hw
  · exact T_closed2 w hw

lemma T_closed_mem (i : Fin 3) (x : W_A3) (hx : x ∈ T) : cs.simple i * x ∈ T := by
  simp only [T, List.mem_toFinset, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact T_closed i w hw

lemma one_mem_T : (1 : W_A3) ∈ T := by
  simp only [T, List.mem_toFinset, List.mem_map]
  exact ⟨[], by simp [Lwords], by simp [cs.wordProd_nil]⟩

lemma wordProd_mem_T : ∀ l : List (Fin 3), cs.wordProd l ∈ T := by
  intro l
  induction l with
  | nil => simpa [cs.wordProd_nil] using one_mem_T
  | cons i l ih => rw [cs.wordProd_cons]; exact T_closed_mem i _ ih

lemma all_mem_T (x : W_A3) : x ∈ T := by
  obtain ⟨l, _, rfl⟩ := cs.exists_reduced_word x
  exact wordProd_mem_T l

instance A3_finite : Finite W_A3 := by
  have hsub : (Set.univ : Set W_A3) ⊆ (↑T : Set W_A3) := fun x _ => all_mem_T x
  exact Set.finite_univ_iff.mp (Set.Finite.subset T.finite_toSet hsub)

lemma card_A3_le : Nat.card W_A3 ≤ 24 := by
  have huniv : (Set.univ : Set W_A3) = (↑T : Set W_A3) :=
    Set.Subset.antisymm (fun x _ => all_mem_T x) (Set.subset_univ _)
  have h1 : Nat.card W_A3 = T.card := by
    rw [← Set.ncard_univ, huniv, Set.ncard_coe_finset]
  rw [h1]
  calc T.card ≤ (Lwords.map cs.wordProd).length := List.toFinset_card_le _
    _ = Lwords.length := by rw [List.length_map]
    _ = 24 := by simp [Lwords]

/-! ### Identification with the symmetric group and the final results -/

def repA3 : Fin 3 → Equiv.Perm (Fin 4) := fun i => Equiv.swap i.castSucc i.succ
theorem hliftA3 : IsLiftable (CoxeterMatrix.Aₙ 3) repA3 := by
  intro i i'; fin_cases i <;> fin_cases i' <;> decide
noncomputable def rhoA3 : W_A3 →* Equiv.Perm (Fin 4) := cs.lift ⟨repA3, hliftA3⟩

theorem rhoA3_surj : Function.Surjective rhoA3 := by
  rw [← MonoidHom.mrange_eq_top, eq_top_iff,
    ← Equiv.Perm.mclosure_swap_castSucc_succ 3, Submonoid.closure_le]
  rintro x ⟨i, rfl⟩
  exact ⟨cs.simple i, by simp only [rhoA3, CoxeterSystem.lift_apply_simple]; rfl⟩

/-- The type-A₃ Coxeter group has exactly 24 elements. -/
theorem card_A3 : Nat.card W_A3 = 24 := by
  refine le_antisymm card_A3_le ?_
  have h : Nat.card (Equiv.Perm (Fin 4)) ≤ Nat.card W_A3 :=
    Nat.card_le_card_of_surjective rhoA3 rhoA3_surj
  simpa using h

/-- A₃ (≅ S₄, order 24) has no element of order 5. -/
theorem W_A3_no_order5 (g : W_A3) : orderOf g ≠ 5 := by
  intro h
  have hdvd : orderOf g ∣ Nat.card W_A3 := orderOf_dvd_natCard g
  rw [h, card_A3] at hdvd
  norm_num at hdvd

end RGF.CoxeterOrdersExp
