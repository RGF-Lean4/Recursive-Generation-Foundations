/-
  Ramsey theory and quintic locking
  Ramsey Theory and Five-Locking

  This file formalizes R(3,3) = 6 and its connection with RGF quintic locking.
-/

import Mathlib

open Finset BigOperators

/-! ## 1. Monochromatic triangles -/

/-- A monochromatic triangle: three distinct vertices whose pairwise edges have the same color. -/
def HasMonoTriangle (n : ℕ) (c : Fin n → Fin n → Bool) : Prop :=
  ∃ (i j k : Fin n), i < j ∧ j < k ∧
    c i j = c j k ∧ c j k = c i k

instance (n : ℕ) (c : Fin n → Fin n → Bool) : Decidable (HasMonoTriangle n c) :=
  inferInstanceAs (Decidable (∃ _, _))

/-! ## 2. R(3,3) > 5: the C₅ counterexample -/

/-- The C₅ coloring: adjacent edges colored true, the rest false. -/
def c5Color : Fin 5 → Fin 5 → Bool := fun i j =>
  decide (((i.val + 1) % 5 = j.val) ∨ ((j.val + 1) % 5 = i.val))

theorem ramsey_lower : ¬ HasMonoTriangle 5 c5Color := by decide

/-! ## 3. R(3,3) ≤ 6 -/

/-
Any 2-coloring of K₆ must contain a monochromatic triangle.

    Proof idea (pigeonhole principle):
    1. Vertex v₀ has 5 edges, 2-colored → at least 3 of the same color
    2. Suppose the edges from v₀ to a, b, c have the same color (say red)
    3. If a-b, b-c, or a-c is red → a red triangle
    4. Otherwise a-b, b-c, a-c are all blue → a blue triangle
-/
theorem ramsey_upper : ∀ (c : Fin 6 → Fin 6 → Bool), HasMonoTriangle 6 c := by
  intro c;
  by_contra! h_contra;
  simp_all +decide [ HasMonoTriangle ];
  -- By the pigeonhole principle, at least 3 of the edges from vertex 0 must be the same color.
  obtain ⟨color, hcolor⟩ : ∃ color : Bool, (Finset.filter (fun j => c 0 j = color) (Finset.Ioi 0)).card ≥ 3 := by
    by_contra! h_contra;
    have h_pigeonhole : (Finset.filter (fun j => c 0 j = true) (Finset.Ioi 0)).card + (Finset.filter (fun j => c 0 j = false) (Finset.Ioi 0)).card = 5 := by
      rw [ Finset.card_filter, Finset.card_filter ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.sum_eq_card_nsmul ] <;> aesop;
    linarith [ h_contra true, h_contra false ];
  -- Let's obtain three vertices $a$, $b$, and $c$ such that $c 0 a = c 0 b = c 0 c = color$.
  obtain ⟨a, b, c', ha, hb, hc', habc⟩ : ∃ a b c' : Fin 6, 0 < a ∧ a < b ∧ b < c' ∧ c 0 a = color ∧ c 0 b = color ∧ c 0 c' = color := by
    simp_all +decide [ Fin.exists_fin_succ ];
    simp_all +decide [ Fin.univ_succ, Finset.filter ];
    erw [ Multiset.filter_cons, Multiset.filter_cons, Multiset.filter_cons, Multiset.filter_cons, Multiset.filter_singleton ] at hcolor ; aesop;
  have := h_contra 0 a ha b hb; have := h_contra 0 a ha c' ( lt_trans hb hc' ) ; have := h_contra 0 b ( lt_trans ha hb ) c' hc'; simp_all +decide ;
  cases h : c a b <;> cases h' : c a c' <;> cases h'' : c b c' <;> simp_all +decide only; all_goals exact h_contra a b hb c' hc' ( by aesop ) ( by aesop )

/-! ## 4. R(3,3) = 6 -/

/-- Complete proof of **R(3,3) = 6**. -/
theorem ramsey_3_3_eq_six :
    (∀ c : Fin 6 → Fin 6 → Bool, HasMonoTriangle 6 c) ∧
    (∃ c : Fin 5 → Fin 5 → Bool, ¬ HasMonoTriangle 5 c) :=
  ⟨ramsey_upper, ⟨c5Color, ramsey_lower⟩⟩

/-! ## 5. Connection with quintic locking -/

/-- The connection between quintic locking and Ramsey theory. -/
theorem five_locking_ramsey_connection :
    -- 5 is the largest complete-graph order avoiding a monochromatic triangle
    (∃ c : Fin 5 → Fin 5 → Bool, ¬ HasMonoTriangle 5 c) ∧
    (∀ c : Fin 6 → Fin 6 → Bool, HasMonoTriangle 6 c) ∧
    -- 5! = 120 = |S₅|
    (Nat.factorial 5 = 120) ∧
    -- φ(5) = 4
    (Nat.totient 5 = 4) :=
  ⟨⟨_, ramsey_lower⟩, ramsey_upper, by decide, by decide⟩