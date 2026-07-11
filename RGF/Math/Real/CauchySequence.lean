/-
  RGF generative real-number system — Cauchy-sequence construction
  Within the dual-layer iteration axiom framework, the reals are constructed from the rationals ℚ via Cauchy sequences.

  Core idea: each step of the dual-layer iteration produces a rational approximation,
  the Cauchy condition guarantees the convergence of the offspring-layer sequence,
  and the equivalence classes correspond to the RGF fixed points (the convergence limits).
-/

import Mathlib

namespace RGF.Real.Cauchy

/-! ## Part 1: Cauchy sequences over the rationals -/

/-- A Cauchy sequence of rationals. -/
def IsCauchyRat (a : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → |a m - a n| < ε

/-- A wrapper type for Cauchy sequences. -/
structure CauchyRatSeq where
  seq : ℕ → ℚ
  is_cauchy : IsCauchyRat seq

/-- A constant sequence is Cauchy. -/
theorem const_isCauchy (q : ℚ) : IsCauchyRat (fun _ => q) := by
  intro ε hε; exact ⟨0, fun m n _ _ => by simp [hε]⟩

/-- A rational embedded as a constant Cauchy sequence. -/
def ofRat (q : ℚ) : CauchyRatSeq := ⟨fun _ => q, const_isCauchy q⟩

/-! ## Part 2: Equivalence relation -/

/-- Two Cauchy sequences are equivalent: their difference tends to zero. -/
def CauchyEquiv (a b : CauchyRatSeq) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a.seq n - b.seq n| < ε

theorem cauchyEquiv_refl (a : CauchyRatSeq) : CauchyEquiv a a := by
  intro ε hε; exact ⟨0, fun n _ => by simp [hε]⟩

theorem cauchyEquiv_symm {a b : CauchyRatSeq} (h : CauchyEquiv a b) : CauchyEquiv b a := by
  intro ε hε; obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by rw [abs_sub_comm]; exact hN n hn⟩

theorem cauchyEquiv_trans {a b c : CauchyRatSeq}
    (hab : CauchyEquiv a b) (hbc : CauchyEquiv b c) : CauchyEquiv a c := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hab (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hbc (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_right hn)
  calc |a.seq n - c.seq n|
      = |(a.seq n - b.seq n) + (b.seq n - c.seq n)| := by ring_nf
    _ ≤ |a.seq n - b.seq n| + |b.seq n - c.seq n| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

theorem cauchyEquiv_equivalence : Equivalence CauchyEquiv :=
  ⟨cauchyEquiv_refl, fun h => cauchyEquiv_symm h, fun h₁ h₂ => cauchyEquiv_trans h₁ h₂⟩

instance : Setoid CauchyRatSeq where
  r := CauchyEquiv
  iseqv := cauchyEquiv_equivalence

/-- A Cauchy real = an equivalence class of Cauchy sequences. -/
def CauchyReal := Quotient (inferInstance : Setoid CauchyRatSeq)

/-! ## Part 3: Addition -/

theorem sum_isCauchy (a b : CauchyRatSeq) : IsCauchyRat (fun n => a.seq n + b.seq n) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := a.is_cauchy (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := b.is_cauchy (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun m n hm hn => ?_⟩
  have h1 := hN₁ m n (le_of_max_le_left hm) (le_of_max_le_left hn)
  have h2 := hN₂ m n (le_of_max_le_right hm) (le_of_max_le_right hn)
  have key : (a.seq m + b.seq m) - (a.seq n + b.seq n) =
    (a.seq m - a.seq n) + (b.seq m - b.seq n) := by ring
  rw [key]
  calc |a.seq m - a.seq n + (b.seq m - b.seq n)|
      ≤ |a.seq m - a.seq n| + |b.seq m - b.seq n| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

def addSeq (a b : CauchyRatSeq) : CauchyRatSeq :=
  ⟨fun n => a.seq n + b.seq n, sum_isCauchy a b⟩

theorem add_respects_equiv {a₁ a₂ b₁ b₂ : CauchyRatSeq}
    (ha : CauchyEquiv a₁ a₂) (hb : CauchyEquiv b₁ b₂) :
    CauchyEquiv (addSeq a₁ b₁) (addSeq a₂ b₂) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hb (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  simp only [addSeq]
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_right hn)
  have key : (a₁.seq n + b₁.seq n) - (a₂.seq n + b₂.seq n) =
    (a₁.seq n - a₂.seq n) + (b₁.seq n - b₂.seq n) := by ring
  rw [key]
  calc |a₁.seq n - a₂.seq n + (b₁.seq n - b₂.seq n)|
      ≤ |a₁.seq n - a₂.seq n| + |b₁.seq n - b₂.seq n| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-! ## Part 4: Boundedness of Cauchy sequences -/

/-
A Cauchy sequence is bounded
-/
theorem cauchy_bounded (a : CauchyRatSeq) :
    ∃ M : ℚ, 0 < M ∧ ∀ n : ℕ, |a.seq n| < M := by
      obtain ⟨ N, hN ⟩ := a.is_cauchy 1 zero_lt_one;
      -- For n ≥ N, |a n| ≤ |a N| + 1 by triangle inequality.
      have h_bound : ∀ n ≥ N, |a.seq n| ≤ |a.seq N| + 1 := by
        exact fun n hn => by cases abs_cases ( a.seq n ) <;> cases abs_cases ( a.seq N ) <;> linarith [ abs_lt.mp ( hN n N hn le_rfl ) ] ;
      -- For n < N, the sequence values are finitely many. Take M = max(|a 0| + 1, ..., |a N| + 1).
      have h_finite : ∃ M : ℚ, ∀ n < N, |a.seq n| ≤ M := by
        exact ⟨ ∑ n ∈ Finset.range N, |a.seq n|, fun n hn => Finset.single_le_sum ( fun n _ => abs_nonneg ( a.seq n ) ) ( Finset.mem_range.mpr hn ) ⟩;
      obtain ⟨ M, hM ⟩ := h_finite; exact ⟨ Max.max ( |a.seq N| + 1 ) M + 1, by positivity, fun n => if hn : n < N then by linarith [ hM n hn, le_max_left ( |a.seq N| + 1 ) M, le_max_right ( |a.seq N| + 1 ) M ] else by linarith [ h_bound n ( le_of_not_gt hn ), le_max_left ( |a.seq N| + 1 ) M, le_max_right ( |a.seq N| + 1 ) M ] ⟩ ;

/-! ## Part 5: Connection with the RGF framework -/

/-- The Cauchy condition implies asymptotic locking. -/
theorem cauchy_eventually_close (a : CauchyRatSeq) (ε : ℚ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → |a.seq m - a.seq n| < ε :=
  a.is_cauchy ε hε

/-- A constant sequence is equivalent to itself (an RGF fixed point). -/
theorem const_is_fixpoint (q : ℚ) : CauchyEquiv (ofRat q) (ofRat q) :=
  cauchyEquiv_refl _

/-- Two sequences converging to the same rational are equivalent. -/
theorem converge_same_implies_equiv (a b : CauchyRatSeq) (q : ℚ)
    (ha : ∀ ε : ℚ, 0 < ε → ∃ N, ∀ n, N ≤ n → |a.seq n - q| < ε)
    (hb : ∀ ε : ℚ, 0 < ε → ∃ N, ∀ n, N ≤ n → |b.seq n - q| < ε) :
    CauchyEquiv a b := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hb (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_right hn)
  calc |a.seq n - b.seq n|
      = |(a.seq n - q) + (q - b.seq n)| := by ring_nf
    _ ≤ |a.seq n - q| + |q - b.seq n| := abs_add_le _ _
    _ = |a.seq n - q| + |b.seq n - q| := by rw [abs_sub_comm q (b.seq n)]
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end RGF.Real.Cauchy