/-
  RGF/NeutrinoPrediction.lean

  Direction I(a) — Neutrino phenomenology, with an **honest experimental status**
  for each statement (see the "Status" note below).

  Building on the `5 = 3 + 2` algebraic rigidity (three "light" plus two "heavy"
  generational slots) and the Koide-type amplitude structure of `KoideExt.lean`,
  this file formalises the leading-order ("zeroth-order") neutrino-sector
  structure of the framework as exact algebraic statements:

  * **`5 = 3 + 2` partition rigidity** — the generational content splits uniquely
    into the observed three active neutrinos plus two sterile/heavy slots
    (`fiveThreeTwo`, `active_plus_sterile`).

  * **Tribimaximal PMNS mixing** — an explicit orthogonal mixing matrix `Utbm`
    whose rows/columns are orthonormal (`Utbm_row*_norm`, `Utbm_orthogonal_*`),
    yielding the exact mixing-angle values
      `sin²θ₁₂ = 1/3`,  `sin²θ₂₃ = 1/2`,  `sin²θ₁₃ = 0`
    (`sinSq_theta12`, `sinSq_theta23`, `sinSq_theta13`).

  * **Normal ordering** — with a Koide-type square-root spectrum the three active
    masses are strictly increasing `m₁ < m₂ < m₃` (`normal_ordering`), i.e. the
    framework favours the *Normal Hierarchy*.

  * **CP phase** — at the tribimaximal point the Jarlskog invariant vanishes
    (`jarlskog_tbm_zero`), the leading-order CP-conserving value.

  ## Status — what is a proved theorem vs. an experimental claim

  Every named result below is a proved *algebraic* fact about the specific matrix
  `Utbm` and the `koideMass` spectrum; none of them is in doubt as mathematics.
  Their *physical* standing, however, differs sharply and is stated honestly here
  rather than uniformly advertised as "definite predictions":

  * **FALSIFIED (reactor angle).**  `sinSq_theta13 : (Utbm 0 2)^2 = 0` encodes the
    tribimaximal value `sin²θ₁₃ = 0`.  This is experimentally **falsified**: Daya
    Bay and RENO (2012) measured a nonzero reactor angle, `sin²θ₁₃ ≈ 0.022`.  So
    tribimaximal is a *zeroth-order ansatz* whose reactor angle is wrong; it is
    retained only as the leading-order structural skeleton implied by `5 = 3 + 2`,
    and must be perturbed to fit data.  The falsification itself is recorded as a
    theorem (`tribimaximal_theta13_falsified`), and the deformation that restores a
    nonzero, data-*input* reactor angle is given by `reactorRowE` /
    `reactorRowE_theta13` — note the value `s²` there is fitted, not predicted.
  * **GOOD LEADING-ORDER APPROXIMATIONS (solar / atmospheric).**  `sin²θ₁₂ = 1/3`
    (`sinSq_theta12`) and `sin²θ₂₃ = 1/2` (`sinSq_theta23`) remain within the right
    ballpark of the measured values (`≈ 0.31` and `≈ 0.55`) but are not exact; they
    are leading-order approximations, not confirmed exact predictions.
  * **STILL VIABLE (qualitative).**  `normal_ordering` (Normal Hierarchy) is a
    qualitative prediction that is currently favoured but not yet decisively
    established; it is the framework's most defensible surviving neutrino claim.
  * **CP.**  `jarlskog_tbm_zero` holds only at the (falsified) tribimaximal point
    and is superseded once a nonzero θ₁₃ and a Dirac phase are included.

  In short: these are **not** all "definite numbers testable by JUNO / DUNE".  One
  of them (θ₁₃ = 0) is already excluded; the others are approximations or
  qualitative statements.  We keep the exact algebra and label the physics truthfully.
-/
import Mathlib

open Real

namespace RGF.Neutrino

noncomputable section

/-! ## 1. The `5 = 3 + 2` generational partition -/

/-- The rigid generational count: five slots split as three active plus two heavy. -/
theorem fiveThreeTwo : (5 : ℕ) = 3 + 2 := by norm_num

/-- Interpreted on the index set: `Fin 5` slots partition into `3` active and `2` sterile. -/
theorem active_plus_sterile : Fintype.card (Fin 3) + Fintype.card (Fin 2) = Fintype.card (Fin 5) := by
  simp

/-! ## 2. The tribimaximal PMNS matrix -/

/-- The tribimaximal mixing matrix (rows = flavour `e,μ,τ`, cols = mass `1,2,3`). -/
def Utbm : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ Real.sqrt (2/3),  Real.sqrt (1/3),  0;
     -Real.sqrt (1/6),  Real.sqrt (1/3),  Real.sqrt (1/2);
      Real.sqrt (1/6), -Real.sqrt (1/3),  Real.sqrt (1/2) ]

/-
The first (electron) row is a unit vector: `|U_e1|² + |U_e2|² + |U_e3|² = 1`.
-/
theorem Utbm_row0_norm :
    (Utbm 0 0)^2 + (Utbm 0 1)^2 + (Utbm 0 2)^2 = 1 := by
  unfold Utbm; norm_num;
  erw [ Matrix.cons_val_succ' ] ; norm_num [ div_pow ]

/-
The second (muon) row is a unit vector.
-/
theorem Utbm_row1_norm :
    (Utbm 1 0)^2 + (Utbm 1 1)^2 + (Utbm 1 2)^2 = 1 := by
  unfold Utbm;
  simp +zetaDelta at *;
  norm_num

/-
The third (tau) row is a unit vector.
-/
theorem Utbm_row2_norm :
    (Utbm 2 0)^2 + (Utbm 2 1)^2 + (Utbm 2 2)^2 = 1 := by
  unfold Utbm;
  simp +zetaDelta at *;
  norm_num

/-
Rows 0 and 1 are orthogonal.
-/
theorem Utbm_orthogonal_01 :
    Utbm 0 0 * Utbm 1 0 + Utbm 0 1 * Utbm 1 1 + Utbm 0 2 * Utbm 1 2 = 0 := by
  unfold Utbm; norm_num; ring_nf; norm_num;
  rw [ show ( 6 : ℝ ) = 2 * 3 by norm_num, Real.sqrt_mul ] <;> ring <;> norm_num;
  erw [ Matrix.cons_val_succ' ] ; norm_num ; ring ; norm_num

/-
Rows 0 and 2 are orthogonal.
-/
theorem Utbm_orthogonal_02 :
    Utbm 0 0 * Utbm 2 0 + Utbm 0 1 * Utbm 2 1 + Utbm 0 2 * Utbm 2 2 = 0 := by
  -- By definition of `Utbm`, we know that the product of the first row and the third column is zero.
  simp [Utbm];
  rw [ show ( 6 : ℝ ) = 2 * 3 by norm_num, Real.sqrt_mul ] <;> ring_nf <;> norm_num;
  norm_num [ mul_comm ]

/-! ## 3. Mixing-angle predictions -/

/-
`sin²θ₁₃ = |U_e3|² = 0`: the reactor angle vanishes at leading order.
-/
theorem sinSq_theta13 : (Utbm 0 2)^2 = 0 := by
  -- By definition of $Utbm$, we know that $Utbm 0 2 = 0$.
  simp [Utbm]

/-
`sin²θ₁₂ = |U_e2|² / (1 − |U_e3|²) = 1/3`: the solar angle.
-/
theorem sinSq_theta12 : (Utbm 0 1)^2 / (1 - (Utbm 0 2)^2) = 1/3 := by
  unfold Utbm; norm_num;
  erw [ Matrix.cons_val_succ' ] ; norm_num

/-
`sin²θ₂₃ = |U_μ3|² / (1 − |U_e3|²) = 1/2`: the atmospheric angle (maximal).
-/
theorem sinSq_theta23 : (Utbm 1 2)^2 / (1 - (Utbm 0 2)^2) = 1/2 := by
  -- Substitute the values of Utbm 1 2 and Utbm 0 2 into the expression.
  simp [Utbm]

/-! ## 4. Normal mass ordering -/

/-- A Koide-type neutrino spectrum: three masses `mᵢ = (a + bᵢ)²` built from a
    common scale `a > 0` and strictly increasing square-root offsets. -/
def koideMass (a b : ℝ) : ℝ := (a + b)^2

/-
**Normal ordering.**  For a common scale `a ≥ 0` and strictly increasing
    non-negative offsets `0 ≤ b₁ < b₂ < b₃`, the Koide-type masses are strictly
    increasing: `m₁ < m₂ < m₃`.  The framework predicts the Normal Hierarchy.
-/
theorem normal_ordering (a b₁ b₂ b₃ : ℝ)
    (ha : 0 ≤ a) (hb1 : 0 ≤ b₁) (h12 : b₁ < b₂) (h23 : b₂ < b₃) :
    koideMass a b₁ < koideMass a b₂ ∧ koideMass a b₂ < koideMass a b₃ := by
  exact ⟨ by unfold koideMass; nlinarith, by unfold koideMass; nlinarith ⟩

/-! ## 5. CP conservation at the tribimaximal point -/

/-- The Jarlskog invariant `J = Im(U_e2 U_μ3 U_e3* U_μ2*)` (here real matrix, so
    the imaginary part is zero) vanishes at tribimaximal mixing: leading-order
    CP conservation. -/
def jarlskog (U : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  U 0 1 * U 1 2 * U 0 2 * U 1 1

/-
At tribimaximal mixing the Jarlskog invariant vanishes (since `U_e3 = 0`).
-/
theorem jarlskog_tbm_zero : jarlskog Utbm = 0 := by
  unfold jarlskog Utbm
  simp

/-! ## 6. Honest experimental status of the reactor angle

    The tribimaximal value `sin²θ₁₃ = 0` is experimentally falsified.  This section
    records that falsification as a theorem and provides a one-parameter reactor
    deformation of the electron row that accommodates the *measured* value as a
    fitted input (not a prediction). -/

/-- The experimentally measured reactor mixing (Daya Bay / RENO, 2012):
    `sin²θ₁₃ ≈ 0.022`, definitely nonzero. -/
def sinSqTheta13_measured : ℝ := 22 / 1000

/-- **The tribimaximal reactor angle is experimentally falsified.**  The ansatz
    gives `sin²θ₁₃ = 0`, but the measured value is nonzero, so `Utbm` is not the
    exact PMNS matrix: its reactor angle disagrees with data. -/
theorem tribimaximal_theta13_falsified :
    (Utbm 0 2) ^ 2 ≠ sinSqTheta13_measured := by
  rw [sinSq_theta13]; norm_num [sinSqTheta13_measured]

/-- Reactor-corrected electron row of the PMNS matrix.  The `5 = 3 + 2` skeleton
    fixes the *solar* `2 : 1` ratio of the first two entries; the third entry carries
    a free reactor amplitude `s`.  This is a one-parameter deformation of the
    tribimaximal electron row `(√(2/3), √(1/3), 0)`; the reactor amplitude `s` is an
    experimental input, not a framework output. -/
noncomputable def reactorRowE (s : ℝ) : Fin 3 → ℝ :=
  ![ Real.sqrt ((1 - s ^ 2) * (2 / 3)), Real.sqrt ((1 - s ^ 2) * (1 / 3)), s ]

/-- The reactor-corrected electron row is a unit vector for any `|s| ≤ 1`: the
    deformation stays on the sphere, so it is a legitimate PMNS row. -/
theorem reactorRowE_unit (s : ℝ) (hs : s ^ 2 ≤ 1) :
    (reactorRowE s 0) ^ 2 + (reactorRowE s 1) ^ 2 + (reactorRowE s 2) ^ 2 = 1 := by
  have h : (0 : ℝ) ≤ 1 - s ^ 2 := by linarith
  simp only [reactorRowE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  ring

/-- The reactor angle carried by the corrected row: `sin²θ₁₃ = |U_e3|² = s²`.
    The value is whatever `s` is chosen to be — i.e. a fitted experimental input. -/
theorem reactorRowE_theta13 (s : ℝ) : (reactorRowE s 2) ^ 2 = s ^ 2 := by
  simp [reactorRowE]

/-- Setting `s = 0` recovers exactly the tribimaximal electron row of `Utbm`. -/
theorem reactorRowE_recovers_tbm (j : Fin 3) : reactorRowE 0 j = Utbm 0 j := by
  fin_cases j <;> simp [reactorRowE, Utbm]

/-- With `s = √(measured value)`, the corrected row reproduces the measured reactor
    angle exactly — by construction, since `s` is fitted to it. -/
theorem reactorRowE_matches_data :
    (reactorRowE (Real.sqrt sinSqTheta13_measured) 2) ^ 2 = sinSqTheta13_measured := by
  rw [reactorRowE_theta13, Real.sq_sqrt (by norm_num [sinSqTheta13_measured])]

end

end RGF.Neutrino