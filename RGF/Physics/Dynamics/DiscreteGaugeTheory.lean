/-
  RGF/DiscreteGaugeTheory.lean

  Direction II — Discrete gauge theory and connections on simplicial complexes.

  A completely explicit, `sorry`-free development of *lattice gauge theory* on a
  simplicial complex, addressing the "electromagnetic screening & vortex
  stability" pain point WITHOUT presupposing a continuous background
  electromagnetic field.  Everything is built purely from discrete geometry:

  * A `ZMod n` (resp. `U(1)`) **connection** is a phase attached to each oriented
    1-simplex (edge), antisymmetric under reversal (`Connection`).
  * The **curvature / plaquette flux** `F(i,j,k)` is the holonomy around an
    oriented triangle — the discrete `d₁` of the connection.
  * **Flux quantization**: over `ZMod n` the flux is automatically valued in
    `ZMod n`; lifted to `U(1)` the loop holonomy is exactly `2πk/n`
    (`u1_holonomy_quantized`).
  * **Bianchi identity / `d² = 0`**: the total flux through the boundary of a
    tetrahedron (`3`-simplex) vanishes (`bianchi_tetrahedron`).
  * **Gauge invariance of the flux** under `A ↦ A + dλ` (`curvature_gauge_invariant`).
  * **Screening ⇔ minimal coupling**: the `U(1)`-covariant gradient energy of a
    charged scalar is invariant under simultaneous phase rotation of the scalar
    and gauge transform of the connection (`coupled_energy_gauge_invariant`);
    this is the precise sense in which the emergent discrete gauge field screens
    the scalar gradient energy — pure discrete geometry, no continuum input.
-/

import Mathlib

open Finset BigOperators
open scoped Real

namespace RGF.Gauge

/-! ## 1. `ZMod n` lattice connections and curvature -/

variable {V : Type*}

/-- A `ZMod n`-valued lattice connection: a phase attached to each oriented edge,
    antisymmetric under edge reversal (a discrete 1-cochain). -/
structure Connection (n : ℕ) (V : Type*) where
  /-- The phase attached to the oriented edge `(i,j)`. -/
  A : V → V → ZMod n
  /-- Antisymmetry under orientation reversal. -/
  antisymm : ∀ i j, A i j = - A j i

/-- The **curvature** (plaquette flux) of a connection around the oriented
    triangle `(i,j,k)`: the holonomy `A i j + A j k + A k i`. -/
def curvature {n : ℕ} (C : Connection n V) (i j k : V) : ZMod n :=
  C.A i j + C.A j k + C.A k i

/-- The curvature is cyclically symmetric (it is a loop holonomy). -/
theorem curvature_cyclic {n : ℕ} (C : Connection n V) (i j k : V) :
    curvature C i j k = curvature C j k i := by
  simp only [curvature]; ring

/-
Reversing the orientation of the triangle negates the flux.
-/
theorem curvature_reverse {n : ℕ} (C : Connection n V) (i j k : V) :
    curvature C i k j = - curvature C i j k := by
  unfold curvature;
  rw [ C.antisymm i j, C.antisymm j k, C.antisymm k i ] ; ring

/-! ## 2. Bianchi identity: `d² = 0` on a tetrahedron -/

/-- **Bianchi identity / `d² = 0`.** The total flux through the (oriented)
    boundary of a tetrahedron `(i,j,k,l)` vanishes: the four triangular faces
    sum to zero.  This is the discrete `d₁ ∘ (curvature)` identity and is the
    source of *flux quantization*: the flux cannot leak, it is a topological
    invariant of each closed surface. -/
theorem bianchi_tetrahedron {n : ℕ} (C : Connection n V) (i j k l : V) :
    curvature C j k l - curvature C i k l + curvature C i j l - curvature C i j k = 0 := by
  simp only [curvature]
  rw [C.antisymm k i, C.antisymm l i, C.antisymm l j]
  ring

/-! ## 3. Gauge transformations -/

/-- A gauge transformation of a connection by a `ZMod n`-valued function on
    vertices: `A ↦ A + dλ`, i.e. `A' i j = A i j + λ j - λ i`. -/
def gaugeTransform {n : ℕ} (C : Connection n V) (lam : V → ZMod n) : Connection n V where
  A := fun i j => C.A i j + lam j - lam i
  antisymm := by
    intro i j
    have h := C.antisymm i j
    rw [h]; ring

/-- **Gauge invariance of the curvature.** The plaquette flux is unchanged by a
    gauge transformation — it is a genuine physical (gauge-invariant)
    observable. -/
theorem curvature_gauge_invariant {n : ℕ} (C : Connection n V) (lam : V → ZMod n)
    (i j k : V) :
    curvature (gaugeTransform C lam) i j k = curvature C i j k := by
  simp only [curvature, gaugeTransform]
  ring

/-- Composition of gauge transformations adds the parameters. -/
theorem gaugeTransform_comp {n : ℕ} (C : Connection n V) (lam mu : V → ZMod n) :
    (gaugeTransform (gaugeTransform C lam) mu).A = (gaugeTransform C (fun v => lam v + mu v)).A := by
  funext i j
  simp only [gaugeTransform]
  ring

/-! ## 4. Lift to `U(1)` and flux quantization -/

/-- The `U(1)` phase associated to an oriented edge of a `ZMod n` connection:
    `φ = (2π/n)·A`, using the canonical representative `A.val ∈ {0,…,n-1}`. -/
noncomputable def u1Phase {n : ℕ} (C : Connection n V) (i j : V) : ℝ :=
  (2 * Real.pi / n) * ((C.A i j).val : ℝ)

/-
**Flux quantization.** The `U(1)` holonomy around a triangle equals
    `2π·k/n` for an integer `k = (curvature).val`, up to the `n`-fold winding of
    the phases: the loop flux is quantized in units of `2π/n`.  Concretely, the
    complex loop holonomy `exp(i·(φ_{ij}+φ_{jk}+φ_{ki}))` equals
    `exp(i·2π·(curvature).val / n)`.
-/
theorem u1_holonomy_quantized {n : ℕ} [NeZero n] (C : Connection n V) (i j k : V) :
    Complex.exp (Complex.I * (u1Phase C i j + u1Phase C j k + u1Phase C k i)) =
    Complex.exp (Complex.I * ((2 * Real.pi / n) * ((curvature C i j k).val : ℝ))) := by
  unfold u1Phase curvature;
  norm_num [ Complex.exp_eq_exp_iff_exists_int ];
  use ((C.A i j).val + (C.A j k).val + (C.A k i).val - (C.A i j + C.A j k + C.A k i).val) / n;
  rw [ Int.cast_div ] <;> norm_num;
  · simp +decide [ ZMod.cast, ZMod.val ] ; ring;
    cases n <;> norm_num at * ; ring;
  · simp +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
  · exact NeZero.ne n

/-! ## 5. Minimal coupling and screening -/

/-- The `U(1)`-covariant discrete gradient energy of a charged scalar field on a
    single oriented edge: `‖φ_j − e^{i A_{ij}} φ_i‖²`.  Here `A i j : ℝ` is a
    real `U(1)` connection phase and `φ : V → ℂ` the charged scalar. -/
noncomputable def edgeCoupledEnergy (A : V → V → ℝ) (phi : V → ℂ) (i j : V) : ℝ :=
  Complex.normSq (phi j - Complex.exp (A i j * Complex.I) * phi i)

/-
**Screening ⇔ minimal coupling (gauge invariance of the coupled energy).**
    Under the simultaneous local phase rotation of the scalar
    `φ_v ↦ e^{i θ_v} φ_v` and the gauge transform of the connection
    `A_{ij} ↦ A_{ij} + θ_j − θ_i`, the covariant edge energy is unchanged.
    This is the exact statement that the emergent discrete gauge field absorbs
    (screens) the scalar phase-gradient energy: the physically meaningful,
    gauge-invariant energy depends only on gauge-invariant data.
-/
theorem coupled_energy_gauge_invariant (A : V → V → ℝ) (phi : V → ℂ)
    (theta : V → ℝ) (i j : V) :
    edgeCoupledEnergy (fun a b => A a b + theta b - theta a)
      (fun v => Complex.exp (theta v * Complex.I) * phi v) i j
      = edgeCoupledEnergy A phi i j := by
  unfold edgeCoupledEnergy; ring;
  norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im, mul_assoc, ← Complex.exp_add ] ; ring;
  norm_num [ Real.sin_add, Real.cos_add ] ; ring;
  rw [ Real.sin_sq, Real.sin_sq ] ; ring;

end RGF.Gauge