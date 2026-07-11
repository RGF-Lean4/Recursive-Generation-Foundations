/-
  RGF/QuantumOrbitPairing.lean

  Direction IV — Operator-algebra generalisation of the non-equilibrium
  "orbit-pairing" theory.

  `OrbitPairing.lean` / `Z5Cancellation.lean` established the orbit-cancellation
  identity for a finite *cyclic* group `Z₅` acting on a classical configuration
  space, controlling the antisymmetric part of an exclusion generator.  This
  module carries that idea in two independent directions requested by Direction
  IV:

  1. **General finite-group cancellation** (non-abelian included).  For *any*
     finite group `G` acting on a space `Ω`, the group-averaged (symmetric) part
     of a kernel and the resulting antisymmetric part obey the exact
     orbit-cancellation identity: the antisymmetric part sums to zero along any
     `G`-orbit (`orbit_cancellation_general`).  This is the promised extension
     from the cyclic `Z₅` case to arbitrary discrete (possibly non-abelian)
     groups.

  2. **Quantum (Lindblad) generalisation.**  The classical Markov generator is
     replaced by an open-quantum-system generator on the non-commutative measure
     space of `n × n` complex matrices.  We define the dissipative Lindblad
     generator and prove its two defining structural properties — trace
     preservation (`lindblad_trace_zero`) and Hermiticity preservation
     (`lindblad_isHermitian` / `lindblad_conjTranspose`) — which make
     `ρ ↦ ρ + t · 𝓛(ρ)` a legitimate infinitesimal quantum channel, the
     non-commutative analogue of the classical stochastic dynamics.

  Contents live in namespace `RGF.QOP`.
-/
import Mathlib

open Finset BigOperators Matrix

namespace RGF.QOP

/-! ## 1. General finite-group orbit cancellation -/

variable {G Ω : Type*} [Group G] [Fintype G]

/-- The group-averaged (symmetric) part of a kernel `gen`, for a left action
    `action : G → Ω → Ω`. -/
noncomputable def symPart (gen : Ω → Ω → ℝ) (action : G → Ω → Ω) (σ τ : Ω) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g : G, gen (action g σ) (action g τ)

/-- The antisymmetric part of the kernel: total minus symmetric. -/
noncomputable def asymPart (gen : Ω → Ω → ℝ) (action : G → Ω → Ω) (σ τ : Ω) : ℝ :=
  gen σ τ - symPart gen action σ τ

/-- Left translation of the summation index by a fixed group element is a
    bijection, so a sum of a function over the group is invariant under it. -/
theorem sum_translate {α : Type*} [AddCommMonoid α] (f : G → α) (h : G) :
    ∑ g : G, f (h * g) = ∑ g : G, f g :=
  Equiv.sum_comp (Equiv.mulLeft h) f

/-
**General orbit-cancellation identity.** For an arbitrary finite group `G`
    acting on `Ω`, the antisymmetric part of the kernel sums to zero along any
    `G`-orbit.  Specialising `G = Z₅` recovers `Z5Cancellation.orbit_cancellation`.
-/
theorem orbit_cancellation_general (gen : Ω → Ω → ℝ) (action : G → Ω → Ω)
    (action_mul : ∀ (g h : G) (σ : Ω), action (g * h) σ = action g (action h σ))
    (σ τ : Ω) :
    ∑ h : G, asymPart gen action (action h σ) (action h τ) = 0 := by
  unfold asymPart; simp +decide ;
  -- By definition of `symPart`, we can rewrite the second sum.
  have h_symPart : ∑ x : G, symPart gen action (action x σ) (action x τ) = (Fintype.card G : ℝ)⁻¹ * ∑ x : G, ∑ g : G, gen (action (g * x) σ) (action (g * x) τ) := by
    rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; simp +decide [ symPart, action_mul ] ;
  rw [ h_symPart, mul_comm, ← Finset.sum_comm ];
  rw [ Finset.sum_congr rfl fun x _ => show ∑ y : G, gen ( action ( x * y ) σ ) ( action ( x * y ) τ ) = ∑ y : G, gen ( action y σ ) ( action y τ ) from Equiv.sum_comp ( Equiv.mulLeft x ) fun y => gen ( action y σ ) ( action y τ ) ] ; simp +decide [ mul_comm, Finset.mul_sum _ _ _, ne_of_gt ( Fintype.card_pos ) ]

/-! ## 2. Quantum Lindblad generator on matrices -/

variable {n m : ℕ}

/-- The **dissipative Lindblad generator** with jump operators `V : Fin m → Mₙ(ℂ)`:
    `𝓛(ρ) = ∑ₖ (Vₖ ρ Vₖ† − ½ (Vₖ†Vₖ ρ + ρ Vₖ†Vₖ))`. -/
noncomputable def lindblad (V : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ k : Fin m, (V k * ρ * (V k)ᴴ
    - (1 / 2 : ℂ) • ((V k)ᴴ * V k * ρ + ρ * (V k)ᴴ * V k))

/-
**Trace preservation.** The Lindblad generator is traceless: `Tr 𝓛(ρ) = 0`.
    This is the infinitesimal form of trace preservation of the quantum channel
    `ρ ↦ ρ + t·𝓛(ρ)`, i.e. conservation of total probability.
-/
theorem lindblad_trace_zero (V : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (lindblad V ρ) = 0 := by
  unfold lindblad; simp +decide [ Matrix.trace_add, Matrix.trace_smul ] ; ring;
  simp +decide [ Matrix.mul_assoc, Matrix.trace_mul_comm ( V _ ) ] ; ring;
  simp +decide [ Matrix.trace_mul_comm ρ, mul_assoc ] ; ring;

/-
**Hermiticity preservation (conjugate-transpose form).**
    `𝓛(ρ)† = 𝓛(ρ†)`: the generator commutes with taking the adjoint.
-/
theorem lindblad_conjTranspose (V : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (lindblad V ρ)ᴴ = lindblad V ρᴴ := by
  unfold lindblad;
  norm_num [ Matrix.conjTranspose_sum, Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul ];
  grind +locals

/-- **Hermiticity preservation.** If `ρ` is Hermitian (a physical density matrix
    is), then so is `𝓛(ρ)`; hence the quantum evolution keeps observables
    self-adjoint. -/
theorem lindblad_isHermitian (V : Fin m → Matrix (Fin n) (Fin n) ℂ)
    {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.IsHermitian) :
    (lindblad V ρ).IsHermitian := by
  show (lindblad V ρ)ᴴ = lindblad V ρ
  rw [lindblad_conjTranspose, hρ.eq]

end RGF.QOP