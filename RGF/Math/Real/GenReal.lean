/-
  RealConstruction/GenReal.lean

  Core definition of the RGF generative reals.
  GenReal is a computable real-number type built from Cauchy sequences of rationals,
  equipped with an equivalence relation (the difference tends to zero) and the quotient type RGFReal.
-/

import Mathlib

namespace RGF

/-! ## Core definition of Cauchy sequences -/

/-- The Cauchy property of a sequence of rationals. -/
def IsCauchySeq (f : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → |f m - f n| < ε

/-- RGF generative reals: computable Cauchy sequences of rationals.
    Each GenReal carries a rational approximation sequence together with a proof of its Cauchy property.
    Computability is manifest: the sequence `approx` is itself a concrete ℕ → ℚ function. -/
structure GenReal where
  /-- The rational approximation sequence. -/
  approx : ℕ → ℚ
  /-- The Cauchy property. -/
  cauchy : IsCauchySeq approx

/-! ## Equivalence relation -/

/-- Two GenReals are equivalent: their difference tends to zero. -/
def GenReal.Equiv (a b : GenReal) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a.approx n - b.approx n| < ε

theorem GenReal.equiv_refl (a : GenReal) : a.Equiv a := by
  intro ε hε; exact ⟨0, fun n _ => by simp [hε]⟩

theorem GenReal.equiv_symm {a b : GenReal} (h : a.Equiv b) : b.Equiv a := by
  intro ε hε; obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by rw [abs_sub_comm]; exact hN n hn⟩

theorem GenReal.equiv_trans {a b c : GenReal}
    (hab : a.Equiv b) (hbc : b.Equiv c) : a.Equiv c := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hab (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hbc (ε / 2) (by linarith)
  exact ⟨max N₁ N₂, fun n hn => by
    calc |a.approx n - c.approx n|
        = |(a.approx n - b.approx n) + (b.approx n - c.approx n)| := by ring_nf
      _ ≤ |a.approx n - b.approx n| + |b.approx n - c.approx n| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := by
          linarith [hN₁ n (le_of_max_le_left hn), hN₂ n (le_of_max_le_right hn)]
      _ = ε := by ring⟩

instance genRealSetoid : Setoid GenReal where
  r := GenReal.Equiv
  iseqv := ⟨GenReal.equiv_refl, fun h => GenReal.equiv_symm h,
            fun h₁ h₂ => GenReal.equiv_trans h₁ h₂⟩

/-- RGF reals: the quotient type of equivalence classes of GenReal. -/
def RGFReal := Quotient genRealSetoid

/-! ## Embedding of the rationals -/

/-- Embed a rational as a constant Cauchy sequence. -/
def GenReal.ofRat (q : ℚ) : GenReal where
  approx := fun _ => q
  cauchy := fun ε hε => ⟨0, fun _ _ _ _ => by simp [hε]⟩

theorem GenReal.ofRat_equiv_iff (p q : ℚ) :
    (GenReal.ofRat p).Equiv (GenReal.ofRat q) ↔ p = q := by
  constructor
  · intro h
    by_contra hne
    have hd : 0 < |p - q| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨N, hN⟩ := h _ hd
    simp [GenReal.ofRat] at hN
    exact absurd (hN N) (lt_irrefl _)
  · intro h; subst h; exact GenReal.equiv_refl _

/-! ## Boundedness -/

/-- A Cauchy sequence is bounded. -/
theorem GenReal.bounded (a : GenReal) :
    ∃ M : ℚ, 0 < M ∧ ∀ n : ℕ, |a.approx n| < M := by
  obtain ⟨N, hN⟩ := a.cauchy 1 one_pos
  -- bound on the tail
  have htail : ∀ n, N ≤ n → |a.approx n| ≤ |a.approx N| + 1 := by
    intro n hn
    have h := hN n N hn le_rfl
    calc |a.approx n| = |a.approx N + (a.approx n - a.approx N)| := by ring_nf
      _ ≤ |a.approx N| + |a.approx n - a.approx N| := abs_add_le _ _
      _ ≤ |a.approx N| + 1 := by linarith
  -- the finite part plus the tail; take the global upper bound
  let finBound := (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N)⟩
    (fun i => (|a.approx i| + 1 : ℚ))
  have hfin : ∀ n ≤ N, |a.approx n| < finBound := by
    intro n hn
    have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have := Finset.le_sup' (fun i => (|a.approx i| + 1 : ℚ)) hmem
    linarith
  refine ⟨max finBound (|a.approx N| + 2), by positivity, fun n => ?_⟩
  by_cases hn : n ≤ N
  · calc |a.approx n| < finBound := hfin n hn
      _ ≤ max finBound (|a.approx N| + 2) := le_max_left _ _
  · push_neg at hn
    calc |a.approx n| ≤ |a.approx N| + 1 := htail n (le_of_lt hn)
      _ < |a.approx N| + 2 := by linarith
      _ ≤ max finBound (|a.approx N| + 2) := le_max_right _ _

end RGF
