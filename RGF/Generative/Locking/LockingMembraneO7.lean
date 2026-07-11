import Mathlib

/-!
# Proposition O7 — Locking-membrane spectral selection of the quintic (`p = 5`)

This file formalises, inside the RGF framework, the machine-verifiable core of
**Proposition O7**.

## Setup (from the statement)

For an odd `p ≥ 5` the FORS propagator kernel
`K̃(k) = [1 + (k/Λ)^{p/2}]⁻¹` has `p` complex poles
`k_j = Λ · exp(i·π·(2j+1)/p)`, `j = 0,…,p-1`.  From these one builds the
linearised drift matrix

`Γ_p := diag(exp(i·π·(2j+1)/p))_{j} · ρ`,  with `ρ ∈ (0,1)`,

a diagonal complex matrix whose diagonal entries are `ρ · exp(i·π·(2j+1)/p)`.

## The locking spectral conditions L1–L2

* **L1** (spectral radius `< 1`): every eigenvalue of `Γ_p` has modulus `ρ`, hence
  the spectral radius is `ρ < 1`.  This holds *trivially for every* odd `p ≥ 5`
  (`Gamma_eigval_abs`, `Gamma_spectralRadius_lt_one`).
* **L2** (all eigenvalues have geometric multiplicity `1`): for a diagonal matrix
  this is exactly the statement that the diagonal entries are pairwise distinct,
  i.e. the pole phases are pairwise distinct.  This too holds for every `p`
  (`poleZ_injective`, `Gamma_eigvals_distinct`).

So L1–L2 alone do **not** single out `p = 5`; they hold for all odd `p ≥ 5`.  The
selection of `p = 5` comes from the *effective contraction factor* on the real
state space,
`κ_p := cos(π/p)`,
together with minimality (the same "smallest admissible parameter" principle that
elsewhere in RGF pins `k_c = 5`).

## The decidable selection principle

* `kappa_strictMono` : `p ↦ cos(π/p)` is strictly increasing, so
  `cos(π/5) < cos(π/7) < cos(π/9) < ⋯ < 1`;
* `argmin_kappa`     : `p = 5` is the unique minimiser of `κ_p` over odd `p ≥ 5`
  (`argmin_{p∈{5,7,9,…}} κ_p = 5`);
* `kappa_five`       : `κ₅ = cos(π/5) = (1 + √5)/4`, i.e. `2·κ₅ = (1+√5)/2`, the
  golden ratio.

> **Correction to the informal statement.**  The prompt writes
> `κ₅ = (√5 − 1)/4`; that number is `cos(2π/5)`, not `cos(π/5)`.  The correct
> value of the maximal real projection is `cos(π/5) = (√5 + 1)/4 ≈ 0.809`, and it
> is this value that satisfies the golden-ratio relation `2·cos(π/5) = φ`.  We
> formalise the corrected value.

The thermodynamic self-consistency `2d − 1 = d + 2` forces `d = 3`
(`thermodynamic_dim`), and the joint solution of the minimality selection with
this dimension constraint is `p = 5`.
-/

open Real Complex

namespace RGF.LockingMembrane.O7

/-! ## Poles, drift matrix, and the effective contraction factor -/

/-- The `j`-th pole phase `exp(i·π·(2j+1)/p)` on the unit circle. -/
noncomputable def poleZ (p : ℕ) (j : ℕ) : ℂ :=
  Complex.exp (Complex.I * Real.pi * (2 * j + 1) / p)

/-- The linearised drift matrix `Γ_p = diag(exp(i·π·(2j+1)/p)) · ρ`. -/
noncomputable def Gamma (p : ℕ) (ρ : ℝ) : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.diagonal (fun j : Fin p => (ρ : ℂ) * poleZ p j)

/-- The effective contraction factor on the real state space,
    `κ_p = cos(π/p)` (the maximal real projection of the pole phases). -/
noncomputable def kappa (p : ℕ) : ℝ := Real.cos (Real.pi / p)

/-! ## L1 — every eigenvalue has modulus `ρ`, so the spectral radius is `ρ < 1` -/

/--
Each pole phase lies on the unit circle.
-/
theorem poleZ_abs (p : ℕ) (j : ℕ) : ‖poleZ p j‖ = 1 := by
  unfold poleZ; norm_num [ Complex.norm_exp ] ;

/--
Every eigenvalue (diagonal entry) of `Γ_p` has modulus `ρ` (for `0 ≤ ρ`).
-/
theorem Gamma_eigval_abs {p : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (j : Fin p) :
    ‖(ρ : ℂ) * poleZ p j‖ = ρ := by
  simp +decide [ abs_of_nonneg hρ, poleZ_abs ]

/--
**L1** holds for every odd `p ≥ 5`: the modulus of each eigenvalue is `ρ < 1`.
-/
theorem Gamma_spectralRadius_lt_one {p : ℕ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (j : Fin p) : ‖(ρ : ℂ) * poleZ p j‖ < 1 := by
  rw [ Gamma_eigval_abs hρ0.le ] ; linarith

/-! ## L2 — the pole phases (hence the eigenvalues) are pairwise distinct -/

/--
The pole phases `j ↦ exp(i·π·(2j+1)/p)` are pairwise distinct on `Fin p`.
    For a diagonal matrix this is exactly "every eigenvalue has geometric
    multiplicity `1`".
-/
theorem poleZ_injective (p : ℕ) :
    Function.Injective (fun j : Fin p => poleZ p j) := by
  intro j j' h_eq
  have h_exp : ∃ n : ℤ, (j : ℂ) - (j' : ℂ) = n * p := by
    unfold poleZ at h_eq;
    rw [ Complex.exp_eq_exp_iff_exists_int ] at h_eq;
    by_cases hp : p = 0 <;> simp_all +decide [ Complex.ext_iff, div_eq_mul_inv ];
    · grind;
    · obtain ⟨ n, hn ⟩ := h_eq; exact ⟨ n, by nlinarith [ Real.pi_pos, mul_inv_cancel_left₀ ( by positivity : ( p : ℝ ) ≠ 0 ) Real.pi ] ⟩ ;
  obtain ⟨ n, hn ⟩ := h_exp; norm_cast at hn; simp_all +decide [ Fin.ext_iff ] ;
  rw [ Int.subNatNat_eq_coe ] at hn ; nlinarith [ show n = 0 by nlinarith [ Fin.is_lt j, Fin.is_lt j' ] ]

/--
**L2** as stated on the eigenvalues of `Γ_p` (for `ρ ≠ 0`): the diagonal
    entries are pairwise distinct.
-/
theorem Gamma_eigvals_distinct {p : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0) :
    Function.Injective (fun j : Fin p => (ρ : ℂ) * poleZ p j) := by
  intro j k h_eq; have := poleZ_injective p; aesop;

/-! ## The decidable selection principle: `argmin κ_p = 5` -/

/--
`κ_p = cos(π/p) < 1` for `p ≥ 2`.
-/
theorem kappa_lt_one {p : ℕ} (hp : 2 ≤ p) : kappa p < 1 := by
  unfold kappa;
  nlinarith [ Real.sin_sq_add_cos_sq ( Real.pi / p ), Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( p : ℝ ) ≥ 2 by norm_cast ] : Real.pi / p < Real.pi ) ]

/--
`p ↦ cos(π/p)` is strictly increasing: for `1 ≤ p < q`, `κ_p < κ_q`.
    In particular `cos(π/5) < cos(π/7) < cos(π/9) < ⋯`.
-/
theorem kappa_strictMono {p q : ℕ} (hp : 1 ≤ p) (hpq : p < q) : kappa p < kappa q := by
  rcases p with ( _ | _ | p ) <;> rcases q with ( _ | _ | q ) <;> norm_num at *;
  · unfold kappa; norm_num;
    exact lt_of_lt_of_le ( by norm_num ) ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ], by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.pi_pos ] ⟩ );
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi ( by positivity ) ( by rw [ div_le_iff₀ ] <;> norm_num <;> nlinarith [ Real.pi_pos ] ) ( by gcongr )

/--
The golden value: `κ₅ = cos(π/5) = (1 + √5)/4`.
-/
theorem kappa_five : kappa 5 = (1 + Real.sqrt 5) / 4 := by
  convert Real.cos_pi_div_five

/--
The golden-ratio relation `2·κ₅ = (1 + √5)/2 = φ`.
-/
theorem kappa_five_golden : 2 * kappa 5 = (1 + Real.sqrt 5) / 2 := by
  rw [kappa_five]; ring

/--
Lower bound: `κ₅ ≤ κ_p` for every odd `p ≥ 5`.
-/
theorem kappa_five_le {p : ℕ} (hodd : Odd p) (hp : 5 ≤ p) : kappa 5 ≤ kappa p := by
  rcases eq_or_lt_of_le hp with rfl | hp' <;> [ norm_num; exact ( by simpa using ( kappa_strictMono ( by decide ) hp' |> le_of_lt ) ) ]

/--
**argmin**: over `p ≥ 5`, the effective contraction factor `κ_p = cos(π/p)`
    is *strictly* minimised only at `p = 5` (in particular over the odd `p ≥ 5`).
-/
theorem argmin_kappa_strict {p : ℕ} (hp : 5 ≤ p) (hne : p ≠ 5) :
    kappa 5 < kappa p :=
  kappa_strictMono (by decide) (lt_of_le_of_ne hp hne.symm)

/--
**`argmin_{p ∈ {5,7,9,…}} κ_p = 5`**: `p = 5` is the unique minimiser of
    `κ_p = cos(π/p)` among odd `p ≥ 5`.
-/
theorem argmin_kappa :
    ∃! p : ℕ, (Odd p ∧ 5 ≤ p) ∧ ∀ q : ℕ, Odd q → 5 ≤ q → kappa p ≤ kappa q := by
  refine' ⟨ 5, _, _ ⟩;
  · exact ⟨ ⟨ by decide, by decide ⟩, fun q hq hq' => kappa_five_le hq hq' ⟩;
  · intro y hy;
    exact le_antisymm ( le_of_not_gt fun h => by linarith [ hy.2 5 ( by decide ) ( by decide ), argmin_kappa_strict hy.1.2 ( by linarith ) ] ) hy.1.2

/-! ## Thermodynamic self-consistency `2d − 1 = d + 2 ⟹ d = 3` -/

/--
The thermodynamic self-consistency condition `2d − 1 = d + 2` has the unique
    solution `d = 3` (for `d ≥ 1`).
-/
theorem thermodynamic_dim {d : ℕ} (hd : 1 ≤ d) : 2 * d - 1 = d + 2 ↔ d = 3 := by
  omega

/-! ## Bundled statement of Proposition O7 -/

/--
**Proposition O7 (machine-verifiable form).**  Bundles the verified content:

* **L1** holds for every odd `p ≥ 5` (spectral radius `ρ < 1`);
* **L2** holds for every odd `p ≥ 5` (eigenvalues pairwise distinct);
* the effective contraction factor `κ_p = cos(π/p)` is strictly increasing, so
  `p = 5` is its unique minimiser over odd `p ≥ 5` (`argmin κ_p = 5`);
* `κ₅ = (1 + √5)/4` with `2·κ₅` the golden ratio;
* the thermodynamic constraint `2d − 1 = d + 2` fixes `d = 3`.
-/
theorem propositionO7 :
    -- L1 : each eigenvalue has modulus `ρ`, so spectral radius `= ρ < 1`
    (∀ (p : ℕ) (ρ : ℝ), 0 < ρ → ρ < 1 → ∀ j : Fin p,
        ‖(ρ : ℂ) * poleZ p j‖ < 1) ∧
    -- L2 : eigenvalues pairwise distinct for every `p` (with `ρ ≠ 0`)
    (∀ (p : ℕ) (ρ : ℝ), ρ ≠ 0 → Function.Injective (fun j : Fin p => (ρ : ℂ) * poleZ p j)) ∧
    -- selection : `argmin_{odd p ≥ 5} cos(π/p) = 5`, uniquely
    (∃! p : ℕ, (Odd p ∧ 5 ≤ p) ∧ ∀ q : ℕ, Odd q → 5 ≤ q → kappa p ≤ kappa q) ∧
    -- golden value at `p = 5`
    kappa 5 = (1 + Real.sqrt 5) / 4 ∧
    -- thermodynamic dimension
    (2 * 3 - 1 = 3 + 2) := by
  exact ⟨ fun p ρ h₀ h₁ j => Gamma_spectralRadius_lt_one h₀ h₁ j, fun p ρ hρ => by simpa using Gamma_eigvals_distinct hρ, argmin_kappa, kappa_five, by norm_num ⟩

end RGF.LockingMembrane.O7