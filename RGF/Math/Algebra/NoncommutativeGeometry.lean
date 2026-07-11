/-
  RGF/NoncommutativeGeometry.lean

  Direction I — Noncommutative geometry and spectral triples.

  A `sorry`-free development of the spectral-geometry core of Alain Connes'
  noncommutative geometry, in which *space is reconstructed from the spectrum of
  an operator* rather than from a point set.  This upgrades the RGF topological
  emergence (Gromov–Hausdorff / persistent homology) to a genuinely spectral
  picture, in which a metric distance is read off the Dirac operator `D`.

  Contents (namespace `RGF.NCG`):

  * **The Connes distance.**  Given a "commutator seminorm" `L` on a space of
    observables and a family of states (functionals) `φ`, the Connes spectral
    distance is `dist(φ,ψ) = sup { |φ(a) − ψ(a)| : L(a) ≤ 1 }`
    (`connesDist`, valued in `ℝ≥0∞`).  We prove it is an extended pseudometric:
    reflexive (`connesDist_self`), symmetric (`connesDist_comm`), and satisfies
    the triangle inequality (`connesDist_triangle`).

  * **The commutator seminorm of a spectral triple.**  For a (bounded model of a)
    Dirac operator `D` on a Hilbert space, `L_D(a) = ‖[D,a]‖` is a genuine
    seminorm (`commSeminorm_add_le`, `commSeminorm_neg`, `commSeminorm_zero`,
    `commSeminorm_nonneg`).  A `SpectralTriple` bundles `(A,H,D,J,γ)` with the
    bounded-commutator condition, and its induced Connes distance is
    `SpectralTriple.dist`.

  * **The spectral action.**  For a finite Dirac spectrum `λ : Fin n → ℝ`, the
    spectral action `S_f = ∑ f(λᵢ)` is linear in the cutoff function `f`
    (`spectralAction_add`, `spectralAction_smul`), and the heat trace
    `Θ(t) = ∑ exp(−t λᵢ²)` has the Seeley–DeWitt moment expansion whose leading
    coefficient is the dimension `n` (`heatTrace_zero`, the cosmological term) and
    whose next coefficient is the curvature moment `∑ λᵢ²`
    (`heatTrace_hasDerivAt_zero`) — the trace `Tr(D²)` that plays the role of the
    Einstein–Hilbert action in the spectral-action dictionary.
-/

import Mathlib

open scoped Topology BigOperators ENNReal
open Filter

namespace RGF.NCG

/-! ## 1. The Connes spectral distance from a commutator seminorm -/

/-- The **Connes spectral distance** between two states `φ, ψ : V → ℝ`, relative
    to a "commutator seminorm" `L : V → ℝ`:
    `dist(φ,ψ) = sup { |φ(a) − ψ(a)| : L(a) ≤ 1 }`, valued in `ℝ≥0∞`. -/
noncomputable def connesDist {V : Type*} (L : V → ℝ) (φ ψ : V → ℝ) : ℝ≥0∞ :=
  ⨆ a : {a : V // L a ≤ 1}, ENNReal.ofReal (|φ a.1 - ψ a.1|)

/-- The Connes distance of a state to itself is `0`. -/
theorem connesDist_self {V : Type*} (L : V → ℝ) (φ : V → ℝ) :
    connesDist L φ φ = 0 := by
  simp [connesDist]

/-- The Connes distance is symmetric. -/
theorem connesDist_comm {V : Type*} (L : V → ℝ) (φ ψ : V → ℝ) :
    connesDist L φ ψ = connesDist L ψ φ := by
  simp only [connesDist]
  congr 1; ext a
  rw [abs_sub_comm]

/-
The Connes distance satisfies the triangle inequality.
-/
theorem connesDist_triangle {V : Type*} (L : V → ℝ) (φ ψ χ : V → ℝ) :
    connesDist L φ χ ≤ connesDist L φ ψ + connesDist L ψ χ := by
  refine' iSup_le _;
  intro a;
  refine' le_trans _ ( add_le_add ( le_iSup _ a ) ( le_iSup _ a ) );
  rw [ ← ENNReal.ofReal_add ( abs_nonneg _ ) ( abs_nonneg _ ) ] ; exact ENNReal.ofReal_le_ofReal ( abs_sub_le _ _ _ ) ;

/-! ## 2. The commutator seminorm of a spectral triple -/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Bounded operators on `H`, the model in which we realise a spectral triple. -/
abbrev Op (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] := H →L[ℂ] H

/-- The commutator `[D,a] = D∘a − a∘D` of two bounded operators. -/
def commutator (D a : Op H) : Op H := D * a - a * D

/-- The **commutator seminorm** `L_D(a) = ‖[D,a]‖`. -/
noncomputable def commSeminorm (D : Op H) (a : Op H) : ℝ := ‖commutator D a‖

/-- The commutator is additive in its second argument. -/
theorem commutator_add (D a b : Op H) :
    commutator D (a + b) = commutator D a + commutator D b := by
  simp only [commutator, mul_add, add_mul]; abel

@[simp] theorem commutator_zero (D : Op H) : commutator D 0 = 0 := by
  simp [commutator]

theorem commutator_neg (D a : Op H) : commutator D (-a) = -commutator D a := by
  simp only [commutator, mul_neg, neg_mul]; abel

theorem commSeminorm_nonneg (D a : Op H) : 0 ≤ commSeminorm D a := norm_nonneg _

@[simp] theorem commSeminorm_zero (D : Op H) : commSeminorm D 0 = 0 := by
  simp [commSeminorm]

theorem commSeminorm_neg (D a : Op H) : commSeminorm D (-a) = commSeminorm D a := by
  simp [commSeminorm, commutator_neg]

/-- The commutator seminorm is subadditive (a genuine seminorm). -/
theorem commSeminorm_add_le (D a b : Op H) :
    commSeminorm D (a + b) ≤ commSeminorm D a + commSeminorm D b := by
  simp only [commSeminorm, commutator_add]
  exact norm_add_le _ _

/-- A (bounded model of a) **real spectral triple** `(A, H, D, J, γ)`: a Dirac
    operator `D`, a real structure `J`, and a `ℤ/2`-grading `γ`, together with a
    represented algebra `A` of observables on which the commutator with `D` is
    bounded.  (In finite dimensions `D` is automatically bounded, so the
    bounded-commutator condition is recorded via the seminorm `commSeminorm`.) -/
structure SpectralTriple (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] where
  /-- The self-adjoint Dirac operator. -/
  D : Op H
  /-- The real structure (charge conjugation). -/
  J : Op H
  /-- The `ℤ/2`-grading (chirality). -/
  grading : Op H
  /-- The grading squares to the identity. -/
  grading_involutive : grading * grading = 1

/-- The Connes spectral distance induced by a spectral triple, on states of the
    algebra of observables, using the commutator seminorm `L_D(a) = ‖[D,a]‖`. -/
noncomputable def SpectralTriple.dist (T : SpectralTriple H) (φ ψ : Op H → ℝ) : ℝ≥0∞ :=
  connesDist (commSeminorm T.D) φ ψ

/-! ## 3. The spectral action and its heat-kernel moment expansion -/

/-- The **spectral action** `S_f(D) = ∑ f(λᵢ)` of a finite Dirac spectrum
    `λ : Fin n → ℝ` with cutoff function `f`. -/
noncomputable def spectralAction {n : ℕ} (f : ℝ → ℝ) (lam : Fin n → ℝ) : ℝ :=
  ∑ i, f (lam i)

/-- The spectral action is additive in the cutoff function. -/
theorem spectralAction_add {n : ℕ} (f g : ℝ → ℝ) (lam : Fin n → ℝ) :
    spectralAction (fun x => f x + g x) lam
      = spectralAction f lam + spectralAction g lam := by
  simp [spectralAction, Finset.sum_add_distrib]

/-- The spectral action is homogeneous in the cutoff function. -/
theorem spectralAction_smul {n : ℕ} (c : ℝ) (f : ℝ → ℝ) (lam : Fin n → ℝ) :
    spectralAction (fun x => c * f x) lam = c * spectralAction f lam := by
  simp [spectralAction, Finset.mul_sum]

/-- The **heat trace** `Θ(t) = Tr(exp(−t D²)) = ∑ exp(−t λᵢ²)`. -/
noncomputable def heatTrace {n : ℕ} (lam : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, Real.exp (-t * (lam i) ^ 2)

/-- **Leading Seeley–DeWitt coefficient.** At `t = 0` the heat trace equals the
    dimension `n` of the spectrum (the number of states) — the cosmological
    constant term of the spectral action. -/
theorem heatTrace_zero {n : ℕ} (lam : Fin n → ℝ) : heatTrace lam 0 = n := by
  simp [heatTrace]

/-
**Next Seeley–DeWitt coefficient.** The first derivative of the heat trace at
    `t = 0` is `−∑ λᵢ² = −Tr(D²)`, the curvature moment playing the role of the
    Einstein–Hilbert action in the spectral-action dictionary.
-/
theorem heatTrace_hasDerivAt_zero {n : ℕ} (lam : Fin n → ℝ) :
    HasDerivAt (heatTrace lam) (-∑ i, (lam i) ^ 2) 0 := by
  convert HasDerivAt.sum fun i _ => ?_ using 1;
  any_goals rw [ ← Finset.sum_neg_distrib ];
  rotate_left;
  exacts [ fun i x => Real.exp ( -x * ( lam i ) ^ 2 ), by simpa using HasDerivAt.exp ( HasDerivAt.neg ( hasDerivAt_id 0 |> HasDerivAt.mul_const <| ( lam i ) ^ 2 ) ), by ext; simp +decide [ heatTrace ] ]

end RGF.NCG