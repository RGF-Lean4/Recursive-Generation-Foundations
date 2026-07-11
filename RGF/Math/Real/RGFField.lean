/-
  Foundations/RGFField.lean

  The RGF reals form a complete field.

  Using the bijective ring homomorphism `RGFReal'.toReal : RGFReal' → ℝ`
  (built in `Foundations.RGFComplete`), we package it as a ring isomorphism
  `RGFReal'.ringEquivReal : RGFReal' ≃+* ℝ`. Since `ℝ` is *the* complete ordered
  field, this exhibits `RGFReal'` as a field isomorphic to `ℝ`.

  We then state and prove Cauchy completeness directly: every sequence of RGF
  reals that is Cauchy (the differences, measured through the canonical map, are
  eventually `≤ 1/(k+1)`) converges to some RGF real.
-/
import Mathlib
import RGF.Generative.Core.RGFComplete

namespace RGF

open RGFNat RGFInt

namespace RGFReal'

/-- The ring isomorphism `RGFReal' ≃+* ℝ`: `RGFReal'` is, as a field, the reals. -/
noncomputable def ringEquivReal : RGFReal' ≃+* ℝ :=
  { equivReal with
    map_mul' := toReal_mul
    map_add' := toReal_add }

@[simp] theorem ringEquivReal_apply (a : RGFReal') : ringEquivReal a = toReal a := rfl

/-- A sequence of RGF reals is Cauchy: its differences (measured through the
    canonical map) are eventually bounded by `1/(k+1)`, for every index `k`. -/
def IsCauchySeqReal (s : ℕ → RGFReal') : Prop :=
  ∀ k : RGFNat, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
    |toReal (s i - s j)| ≤ 1 / ((k.toNat : ℚ) + 1)

/-
**Completeness of the RGF reals.** Every Cauchy sequence of RGF reals
    converges to an RGF real.
-/
theorem complete (s : ℕ → RGFReal') (h : IsCauchySeqReal s) :
    ∃ L : RGFReal', ∀ k : RGFNat, ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      |toReal (s i - L)| ≤ 1 / ((k.toNat : ℚ) + 1) := by
  have h_cauchy : CauchySeq (fun n => toReal (s n)) := by
    rw [ Metric.cauchySeq_iff ];
    intro ε hε
    obtain ⟨k, hk⟩ : ∃ k : RGFNat, 1 / ((k.toNat : ℚ) + 1) < ε := by
      rcases exists_nat_one_div_lt hε with ⟨ k, hk ⟩;
      use RGFNat.ofNat' k;
      convert hk using 1;
      congr! 2;
      exact_mod_cast RGFNat.toNat_ofNat k;
    obtain ⟨ N, hN ⟩ := h k;
    exact ⟨ N, fun m hm n hn => by simpa [ dist_eq_norm, RGFReal'.toReal_sub ] using lt_of_le_of_lt ( hN m n hm hn ) hk ⟩;
  obtain ⟨ L, hL ⟩ := cauchySeq_tendsto_of_complete h_cauchy;
  obtain ⟨ L', hL' ⟩ := RGFReal'.toReal_surjective L;
  refine' ⟨ L', fun k => _ ⟩;
  have := h k;
  obtain ⟨ N, hN ⟩ := this; use N; intro i hi; have := hN i i hi hi; simp_all +decide [ RGFReal'.toReal_sub ] ;
  exact le_of_tendsto ( Filter.Tendsto.abs ( tendsto_const_nhds.sub hL ) ) ( Filter.eventually_atTop.mpr ⟨ N, fun j hj => hN i j hi hj ⟩ )

/-! ## Field axioms for `RGFReal'`

The native operations on `RGFReal'` (defined from scratch on Cauchy sequences)
satisfy every field axiom.  Each is proved by transporting through the injective
ring homomorphism `toReal` and using the corresponding fact in `ℝ`; this is
mathematically a *native* proof, since `toReal` is determined by the RGF
operations themselves (`toReal_add`, `toReal_mul`, …). -/

theorem add_assoc' (a b c : RGFReal') : a + b + c = a + (b + c) :=
  toReal_injective (by simp only [toReal_add]; ring)

theorem add_comm' (a b : RGFReal') : a + b = b + a :=
  toReal_injective (by simp only [toReal_add]; ring)

theorem zero_add' (a : RGFReal') : 0 + a = a :=
  toReal_injective (by simp only [toReal_add, toReal_zero]; ring)

theorem add_zero' (a : RGFReal') : a + 0 = a :=
  toReal_injective (by simp only [toReal_add, toReal_zero]; ring)

theorem neg_add_cancel' (a : RGFReal') : neg a + a = 0 :=
  toReal_injective (by simp only [toReal_add, toReal_neg, toReal_zero]; ring)

theorem add_neg_cancel' (a : RGFReal') : a + neg a = 0 :=
  toReal_injective (by simp only [toReal_add, toReal_neg, toReal_zero]; ring)

theorem mul_assoc' (a b c : RGFReal') : a * b * c = a * (b * c) :=
  toReal_injective (by simp only [toReal_mul]; ring)

theorem mul_comm' (a b : RGFReal') : a * b = b * a :=
  toReal_injective (by simp only [toReal_mul]; ring)

theorem one_mul' (a : RGFReal') : 1 * a = a :=
  toReal_injective (by simp only [toReal_mul, toReal_one]; ring)

theorem mul_one' (a : RGFReal') : a * 1 = a :=
  toReal_injective (by simp only [toReal_mul, toReal_one]; ring)

theorem left_distrib' (a b c : RGFReal') : a * (b + c) = a * b + a * c :=
  toReal_injective (by simp only [toReal_mul, toReal_add]; ring)

theorem right_distrib' (a b c : RGFReal') : (a + b) * c = a * c + b * c :=
  toReal_injective (by simp only [toReal_mul, toReal_add]; ring)

theorem zero_ne_one' : (0 : RGFReal') ≠ 1 := by
  intro h
  have : (0 : ℝ) = 1 := by rw [← toReal_zero, ← toReal_one, h]
  exact zero_ne_one this

/-- Multiplicative inverse on `RGFReal'`, given through the canonical bijection. -/
noncomputable def inv (a : RGFReal') : RGFReal' := equivReal.symm (toReal a)⁻¹

@[simp] theorem toReal_inv (a : RGFReal') : toReal (inv a) = (toReal a)⁻¹ := by
  show equivReal (equivReal.symm (toReal a)⁻¹) = (toReal a)⁻¹
  exact equivReal.apply_symm_apply _

/-- Every nonzero RGF real has a multiplicative inverse. -/
theorem mul_inv_cancel' (a : RGFReal') (ha : a ≠ 0) : a * inv a = 1 := by
  apply toReal_injective
  rw [toReal_mul, toReal_inv, toReal_one]
  refine mul_inv_cancel₀ ?_
  intro h
  exact ha (toReal_injective (by rw [h, toReal_zero]))

end RGFReal'
end RGF