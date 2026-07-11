import Mathlib

/-!
# Koide-relation extensions: symmetric polynomials, characteristic cubic,
# orbit synchronization, and particle–hole symmetry

This file develops a self-contained algebraic theory around the three "mass
amplitudes"
`v k δ = 1 + √2 · cos(δ + 2πk/3)`  (k = 0,1,2),
the same amplitudes underlying the Koide relation `(Σ v²)/(Σ v)² = 2/3`.

## Main results

### Symmetric polynomials of the three amplitudes
* `koide_triple_cos_prod` — `cos δ · cos(δ+2π/3) · cos(δ+4π/3) = (1/4) cos 3δ`.
* `koide_val_sum_explicit` — first symmetric polynomial `v₀+v₁+v₂ = 3`.
* `koide_e2` — second symmetric polynomial `v₀v₁+v₀v₂+v₁v₂ = 3/2` (δ-independent).
* `koide_val_prod` — product `v₀·v₁·v₂ = -1/2 + (√2/2) cos 3δ` (the unique
  δ-carrying symmetric quantity).
* `koide_cubic_factor` — the three amplitudes are the roots of one monic cubic.
* `koide_val_is_root` — each amplitude solves that characteristic cubic.
* `koideMatrix_det` — determinant of the spectral (diagonalized circulant)
  matrix equals the product of the three eigenvalues.
* `koide_mass_prod` — product of the three masses `∏ m_k = ∏ v_k²`.

### Initial-value forgetting / orbit synchronization
* `drivenSeq_sub_initial` — the difference of two driven recursions sharing the
  same forcing has the closed form `cⁿ·(z₀-z₀')`, independent of the forcing.
* `drivenSeq_synchronization` — for `|c|<1` that difference tends to `0`.

### Particle–hole symmetry of the macroscopic current
* `current_particle_hole` — `j(ρ)=ρ(1-ρ)` is invariant under `ρ ↦ 1-ρ`.
* `current_le_quarter`, `current_eq_quarter_iff` — `j(ρ) ≤ 1/4`, with equality
  iff `ρ = 1/2`.
* `emergent_mean_particle_hole`, `emergent_mean_le_quarter`,
  `emergent_mean_max_at_half` — the corresponding facts for the emergent mean
  `j(ρ)/(1-c)`.
-/

namespace TRS.LeptonKoideExt

open Real

noncomputable section

/-- The three "mass amplitudes" `v k δ = 1 + √2 cos(δ + 2πk/3)`. -/
def v (k : ℕ) (δ : ℝ) : ℝ := 1 + Real.sqrt 2 * Real.cos (δ + 2 * Real.pi * k / 3)

/-
Classic three-phase cosine product identity.
-/
lemma koide_triple_cos_prod (δ : ℝ) :
    Real.cos δ * Real.cos (δ + 2 * Real.pi / 3) * Real.cos (δ + 4 * Real.pi / 3)
      = (1 / 4) * Real.cos (3 * δ) := by
  norm_num [ ( by ring : 3 * δ = δ + δ + δ ), ( by ring : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 ), ( by ring : 4 * Real.pi / 3 = Real.pi + Real.pi / 3 ), Real.cos_add ] ; ring;
  rw [ show δ * 2 = δ + δ by ring, Real.sin_add ] ; rw [ show Real.pi * ( 4 / 3 ) = Real.pi + Real.pi / 3 by ring ] ; norm_num [ Real.sin_add, Real.cos_add ] ; ring;
  norm_num ; ring

/-
First elementary symmetric polynomial: `v₀+v₁+v₂ = 3`.
-/
lemma koide_val_sum_explicit (δ : ℝ) : v 0 δ + v 1 δ + v 2 δ = 3 := by
  unfold v;
  norm_num [ show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, show 4 * Real.pi / 3 = Real.pi + Real.pi / 3 by ring, Real.cos_add ] ; ring;
  rw [ show Real.pi * ( 4 / 3 ) = Real.pi + Real.pi / 3 by ring, Real.cos_add, Real.sin_add ] ; norm_num ; ring;

/-
Second elementary symmetric polynomial: `v₀v₁+v₀v₂+v₁v₂ = 3/2`.
-/
lemma koide_e2 (δ : ℝ) :
    v 0 δ * v 1 δ + v 0 δ * v 2 δ + v 1 δ * v 2 δ = 3 / 2 := by
  unfold v;
  norm_num [ show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, show 4 * Real.pi / 3 = Real.pi + Real.pi / 3 by ring, Real.cos_add, Real.sin_add ] ; ring;
  rw [ show Real.pi * ( 4 / 3 ) = Real.pi + Real.pi / 3 by ring, Real.cos_add, Real.sin_add ] ; norm_num ; ring ; norm_num [ Real.sin_sq, Real.cos_sq ] ; ring;

/-
Product law: `v₀·v₁·v₂ = -1/2 + (√2/2) cos 3δ`.
-/
lemma koide_val_prod (δ : ℝ) :
    v 0 δ * v 1 δ * v 2 δ = -1 / 2 + (Real.sqrt 2 / 2) * Real.cos (3 * δ) := by
  unfold v;
  norm_num [ ( by ring : 3 * δ = δ + δ + δ ), Real.sin_add, Real.cos_add, ( by ring : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 ), ( by ring : 2 * Real.pi * 2 / 3 = Real.pi + Real.pi / 3 ), Real.sin_sub, Real.sin_add, Real.cos_sub, Real.cos_add ] ; ring_nf ; norm_num ; ring_nf;
  rw [ Real.sin_sq ] ; norm_num [ pow_three ] ; ring;

/-
The three amplitudes are the roots of one monic cubic
`t³ - 3t² + (3/2)t - (v₀v₁v₂) = (t-v₀)(t-v₁)(t-v₂)`.
-/
lemma koide_cubic_factor (δ t : ℝ) :
    t ^ 3 - 3 * t ^ 2 + (3 / 2) * t - v 0 δ * v 1 δ * v 2 δ
      = (t - v 0 δ) * (t - v 1 δ) * (t - v 2 δ) := by
  unfold v;
  norm_num [ Real.cos_add ] ; ring;
  rw [ show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring, show Real.pi * ( 4 / 3 ) = Real.pi + Real.pi / 3 by ring ] ; norm_num [ Real.sin_add, Real.cos_add ] ; ring;
  norm_num [ Real.sin_sq ] ; ring

/-
Each amplitude `v_k` (k<3) solves the characteristic cubic.
-/
lemma koide_val_is_root (δ : ℝ) (k : ℕ) (hk : k < 3) :
    (v k δ) ^ 3 - 3 * (v k δ) ^ 2 + (3 / 2) * (v k δ) - v 0 δ * v 1 δ * v 2 δ = 0 := by
  interval_cases k <;> norm_num [ koide_cubic_factor ]

/-- The spectral (diagonalized circulant) Koide matrix whose diagonal carries the
three eigen-amplitudes. -/
def koideMatrix (δ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![v 0 δ, v 1 δ, v 2 δ]

/-
Determinant of the Koide matrix equals the product of the three eigenvalues,
i.e. `-1/2 + (√2/2) cos 3δ`.
-/
lemma koideMatrix_det (δ : ℝ) :
    (koideMatrix δ).det = -1 / 2 + (Real.sqrt 2 / 2) * Real.cos (3 * δ) := by
  rw [ ← koide_val_prod δ, koideMatrix ];
  norm_num [ mul_assoc ];
  rw [ Fin.prod_univ_three ] ; ring!

/-
Product of the three masses `m_k = v_k²`: `∏ m_k = (∏ v_k)²`.
-/
lemma koide_mass_prod (δ : ℝ) :
    (v 0 δ) ^ 2 * (v 1 δ) ^ 2 * (v 2 δ) ^ 2
      = (-1 / 2 + (Real.sqrt 2 / 2) * Real.cos (3 * δ)) ^ 2 := by
  rw [ ← koide_val_prod δ, mul_pow, mul_pow ]

/-! ## Initial-value forgetting / orbit synchronization -/

/-- A driven (forced) linear recursion `z_{n+1} = c·z_n + drive n`. -/
def drivenSeq (c z0 : ℝ) (drive : ℕ → ℝ) : ℕ → ℝ
  | 0 => z0
  | (n + 1) => c * drivenSeq c z0 drive n + drive n

/-
The difference of two driven recursions sharing the same forcing has the
closed form `cⁿ·(z₀-z₀')`, completely independent of the forcing.
-/
lemma drivenSeq_sub_initial (c z0 z0' : ℝ) (drive : ℕ → ℝ) (n : ℕ) :
    drivenSeq c z0 drive n - drivenSeq c z0' drive n = c ^ n * (z0 - z0') := by
  induction' n with n ih <;> simp_all +decide [ pow_succ', mul_assoc ];
  · rfl;
  · rw [ ← ih ] ; rw [ show drivenSeq c z0 drive ( n + 1 ) = c * drivenSeq c z0 drive n + drive n from rfl, show drivenSeq c z0' drive ( n + 1 ) = c * drivenSeq c z0' drive n + drive n from rfl ] ; ring;

/-
For a contraction `|c|<1`, two driven orbits with different initial data
synchronize: their difference tends to `0`.
-/
lemma drivenSeq_synchronization (c z0 z0' : ℝ) (drive : ℕ → ℝ) (hc : |c| < 1) :
    Filter.Tendsto (fun n => drivenSeq c z0 drive n - drivenSeq c z0' drive n)
      Filter.atTop (nhds 0) := by
  simpa [ drivenSeq_sub_initial ] using Filter.Tendsto.mul ( tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc ) tendsto_const_nhds

/-! ## Particle–hole symmetry of the macroscopic current -/

/-- The macroscopic current `j(ρ) = ρ(1-ρ)`. -/
def current (ρ : ℝ) : ℝ := ρ * (1 - ρ)

/-
The current is invariant under the particle–hole transformation `ρ ↦ 1-ρ`.
-/
lemma current_particle_hole (ρ : ℝ) : current (1 - ρ) = current ρ := by
  unfold current; ring;

/-
The current is bounded above by `1/4`.
-/
lemma current_le_quarter (ρ : ℝ) : current ρ ≤ 1 / 4 := by
  unfold current; nlinarith [ sq_nonneg ( ρ - 1 / 2 ) ] ;

/-
The current attains `1/4` exactly at the half-filling density `ρ = 1/2`.
-/
lemma current_eq_quarter_iff (ρ : ℝ) : current ρ = 1 / 4 ↔ ρ = 1 / 2 := by
  constructor <;> intro h <;> unfold current at * <;> nlinarith [ sq_nonneg ( ρ - 1 / 2 ) ] ;

/-- The emergent stationary mean `j(ρ)/(1-c)`. -/
def emergent_mean (ρ c : ℝ) : ℝ := current ρ / (1 - c)

/-
The emergent mean is particle–hole symmetric.
-/
lemma emergent_mean_particle_hole (ρ c : ℝ) :
    emergent_mean (1 - ρ) c = emergent_mean ρ c := by
  unfold emergent_mean current; ring;

/-
For `c < 1`, the emergent mean is bounded above by `(1/4)/(1-c)`.
-/
lemma emergent_mean_le_quarter (ρ c : ℝ) (hc : c < 1) :
    emergent_mean ρ c ≤ (1 / 4) / (1 - c) := by
  exact div_le_div_of_nonneg_right ( current_le_quarter ρ ) ( by linarith )

/-
The emergent-mean upper bound is achieved at half filling `ρ = 1/2`.
-/
lemma emergent_mean_max_at_half (c : ℝ) :
    emergent_mean (1 / 2) c = (1 / 4) / (1 - c) := by
  unfold emergent_mean current; norm_num;

end

end TRS.LeptonKoideExt