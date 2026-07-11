/-
  Paper 3S — "Supplementary material: from RCD lattice rules to the time-domain recursion equation"
  (Supplement: from lattice rules to the time-domain recursion equation),
  L. Sun 2026.

  Placed in the RGF `Physics/Emergence` layer.  Formalizes the properties of the
  time–space coarse-graining (TRCG) operator (§SM-01) that turn microscopic
  lattice rules into the coarse-grained recursion `Ψ_{n+1} = R[Ψ_n] + ξ_n`:

  * the TRCG density field `ρ_CG = (1/N)∑ nᵧ` is a genuine occupation fraction:
    for occupation numbers `nᵧ ∈ {0,1}` (indeed `∈ [0,1]`), `ρ_CG ∈ [0,1]`
    (eq. (SM.1));
  * the mean/fluctuation decomposition `ρ_CG = ρ̄ + δρ` has a *zero-mean*
    fluctuation `∑ (nᵧ − ρ_CG) = 0` (eqs. (SM.2)–(SM.3));
  * the zero-noise recursion `Ψ ↦ R[Ψ]` iterated `n` times is `R^[n]`
    (eq. (SM.4) with `ξ ≡ 0`).
-/
import Mathlib

namespace RGF.Paper3S

variable {N : ℕ}

/-- Coarse-grained occupation fraction `ρ_CG = (1/N)∑ f i` (eq. (SM.1)). -/
noncomputable def coarseAverage (N : ℕ) (f : Fin N → ℝ) : ℝ :=
  (∑ i, f i) / N

/-- The TRCG density field is a genuine occupation fraction: if every occupation
number lies in `[0,1]`, then `ρ_CG ∈ [0,1]`. -/
theorem coarseAverage_mem_unitInterval (f : Fin N → ℝ)
    (h : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    0 ≤ coarseAverage N f ∧ coarseAverage N f ≤ 1 := by
  exact ⟨ div_nonneg ( Finset.sum_nonneg fun _ _ => h _ |>.1 ) ( Nat.cast_nonneg _ ), div_le_one_of_le₀ ( le_trans ( Finset.sum_le_sum fun _ _ => h _ |>.2 ) ( by norm_num ) ) ( Nat.cast_nonneg _ ) ⟩

/-- Mean/fluctuation decomposition (eqs. (SM.2)–(SM.3)): the fluctuation field
`δρ = nᵧ − ρ_CG` has zero mean, `∑ (f i − ρ_CG) = 0`. -/
theorem fluctuation_mean_zero (hN : 0 < N) (f : Fin N → ℝ) :
    ∑ i, (f i - coarseAverage N f) = 0 := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, coarseAverage, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hNne, sub_self]

/-- Zero-noise recursion (eq. (SM.4) with `ξ ≡ 0`): each coarse-grained step
applies the generative map `R`, so the `(n+1)`-step evolution is `R` applied to
the `n`-step evolution. -/
theorem zero_noise_recursion_step {α : Type*} (R : α → α) (n : ℕ) (Ψ : α) :
    R^[n + 1] Ψ = R (R^[n] Ψ) := Function.iterate_succ_apply' R n Ψ

end RGF.Paper3S