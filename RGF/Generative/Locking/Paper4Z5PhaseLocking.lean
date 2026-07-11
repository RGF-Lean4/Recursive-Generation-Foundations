/-
  Paper 4 (+ 4S) — "Phase-locking emergence of the Z5 symmetry in Recursive Constitutive Dynamics"
  (Phase-locking emergence of the Z5 symmetry), L. Sun 2026.

  Placed in the RGF `Generative/Locking` layer.  Formalizes the paper's core
  selection arithmetic for the locking order `p`:

  * the real-axis effective compression factor `κ_p = cos(π/p)`;
  * `κ₅ = cos(π/5) = (1+√5)/4`, with the golden-ratio relation `2κ₅ = (1+√5)/2 = φ`
    (this corrects the erratum noted in the paper: `(√5−1)/4` is `cos(2π/5)`, not
    `cos(π/5)`);
  * strict monotonicity of `κ_p` in `p` (illustrated by `κ₅ < κ₇`), so `p = 5` is
    the minimal-compression, dynamically stable choice among odd `p ≥ 5`;
  * the thermodynamic self-consistency `2d − 1 = d + 2 ⟺ d = 3`.
-/
import Mathlib

open Real

namespace RGF.Paper4

/-- Real-axis effective compression factor of the order-`p` drift matrix. -/
noncomputable def kappa (p : ℕ) : ℝ := Real.cos (π / p)

/-- `κ₅ = cos(π/5) = (1+√5)/4` (corrected value). -/
theorem kappa_five : kappa 5 = (1 + Real.sqrt 5) / 4 := by
  unfold kappa; norm_num [Real.cos_pi_div_five]

/-- Golden-ratio relation `2·κ₅ = (1+√5)/2 = φ`. -/
theorem kappa_five_golden : 2 * kappa 5 = (1 + Real.sqrt 5) / 2 := by
  rw [kappa_five]; ring

/-
Strict monotonicity instance `κ₅ < κ₇`: since `cos` is strictly decreasing on
`[0,π]` and `π/5 > π/7`, the compression factor increases with `p`, so `p = 5`
gives the smallest `κ_p`.
-/
theorem kappa_five_lt_seven : kappa 5 < kappa 7 := by
  exact Real.cos_lt_cos_of_nonneg_of_le_pi ( by positivity ) ( by linarith [ Real.pi_pos ] ) ( by linarith [ Real.pi_pos ] )

/-- Thermodynamic self-consistency: `2d − 1 = d + 2` iff `d = 3` (for `d ≥ 1`). -/
theorem thermodynamic_dim (d : ℕ) (hd : 1 ≤ d) : 2 * d - 1 = d + 2 ↔ d = 3 := by
  omega

/-- Pole phase `e^{iπ(2j+1)/p}` of the FORS kernel (Paper 4 definition `poleZ`). -/
noncomputable def poleZ (p j : ℕ) : ℂ := Complex.exp (Complex.I * (π * (2 * j + 1) / p))

/-
The five order-5 pole phases are pairwise distinct (L2 geometric
multiplicity one): `poleZ 5` is injective on `Fin 5`.
-/
theorem poleZ_five_injective :
    Function.Injective (fun j : Fin 5 => poleZ 5 j) := by
  intro a b h;
  -- Apply the injectivity of the exponential function to conclude that the arguments must be equal modulo $2\pi$.
  have h_mod : ∃ n : ℤ, (a : ℝ) - (b : ℝ) = 5 * n := by
    obtain ⟨ n, hn ⟩ := Complex.exp_eq_exp_iff_exists_int.mp h;
    exact ⟨ n, by norm_num [ Complex.ext_iff ] at hn; nlinarith [ Real.pi_pos ] ⟩;
  obtain ⟨ n, hn ⟩ := h_mod; exact Fin.ext ( by rw [ sub_eq_iff_eq_add ] at hn; norm_cast at hn; omega ) ;

end RGF.Paper4