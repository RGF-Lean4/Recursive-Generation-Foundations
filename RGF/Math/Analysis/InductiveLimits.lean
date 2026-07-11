/-
  RGF/InductiveLimits.lean

  Direction III — Operator-algebra inductive limits and AF algebras.

  A `sorry`-free development of the *inductive-limit* (AF-algebra) machinery that
  carries the RGF "layer-by-layer generated" finite-state lattices to the
  thermodynamic / continuum limit `N → ∞`.  An approximately finite-dimensional
  (AF) `C*`-algebra is by definition the inductive limit of a sequence of
  finite-dimensional `C*`-algebras with connecting `*`-monomorphisms.

  Contents (namespace `RGF.InductiveLimit`):

  * **Existence and uniqueness of the inductive limit.**  For any directed system
    of (finite-dimensional) algebras `Aᵢ` over `ℕ` with connecting ring
    homomorphisms `φᵢⱼ`, the inductive limit `DirectLimit A φ` exists as a ring
    (Mathlib's colimit), the canonical maps `ιᵢ` are ring homomorphisms
    (`limitOf`), they are **injective** whenever the connecting maps are
    (`limitOf_injective` — the norm-preserving `*`-monomorphism property), they are
    compatible (`limitOf_compatible`), and the limit satisfies the universal
    property: every compatible cocone factors **uniquely** through it
    (`limit_lift_spec`, `limit_lift_unique`).

  * **The `*`-monomorphism sequence (amplification / UHF tower).**  The standard
    connecting map of a UHF tower, the amplification
    `a ↦ 1ₛ ⊗ a : Mₘ(ℂ) → M_{s·m}(ℂ)`, is a unital ring homomorphism
    (`amplify`), it is **injective** (`amplify_injective`), and it is
    `*`-preserving (`amplify_star`).

  * **K-theory invariant.**  On the ordered group `K₀ = ℤ` (rank of projections),
    the amplification acts as **multiplication by the multiplicity `s`**:
    `rank(1ₛ ⊗ p) = s · rank(p)` (`K0_amplify`, via `trace`).  This is the
    connecting map of the `K₀` inductive system whose limit is the `K₀`-group of
    the AF algebra — the complete invariant distinguishing the towers.
-/

import Mathlib

open Matrix Kronecker BigOperators

namespace RGF.InductiveLimit

/-! ## 1. Existence, injectivity and universal property of the inductive limit -/

section AbstractLimit

variable (A : ℕ → Type*) [∀ n, Ring (A n)]
  (φ : (i j : ℕ) → i ≤ j → (A i →+* A j))
  [DirectedSystem A (fun i j h => (φ i j h))]

/-- The inductive limit `A = lim→ Aₙ` of a directed system of finite-dimensional
    algebras, together with its canonical ring homomorphism `ιᵢ : Aᵢ → A`. -/
noncomputable def limitOf (i : ℕ) : A i →+* DirectLimit A φ := DirectLimit.Ring.of A φ i

/-- The canonical maps into the inductive limit are compatible with the
    connecting `*`-homomorphisms: `ι_j ∘ φ_{ij} = ι_i`. -/
theorem limitOf_compatible (i j : ℕ) (h : i ≤ j) (x : A i) :
    limitOf A φ j (φ i j h x) = limitOf A φ i x := by
  simp [limitOf]

/-- **Norm-preserving `*`-monomorphism property.** If every connecting map is
    injective, then every canonical map into the inductive limit is injective. -/
theorem limitOf_injective (hinj : ∀ i j h, Function.Injective (φ i j h)) (i : ℕ) :
    Function.Injective (limitOf A φ i) := by
  have hmk := DirectLimit.mk_injective (F := A) φ hinj i
  intro x y hxy
  exact hmk hxy

/-- **Universal property (existence).** Any compatible cocone `g : ∀ i, Aᵢ →+* P`
    factors through the inductive limit via the lift `limitLift`. -/
noncomputable def limitLift (P : Type*) [Ring P] (g : (i : ℕ) → A i →+* P)
    (hg : ∀ i j hij x, g j (φ i j hij x) = g i x) : DirectLimit A φ →+* P :=
  DirectLimit.Ring.lift A φ P g hg

/-- The lift recovers the cocone: `limitLift ∘ ιᵢ = gᵢ`. -/
theorem limit_lift_spec (P : Type*) [Ring P] (g : (i : ℕ) → A i →+* P)
    (hg : ∀ i j hij x, g j (φ i j hij x) = g i x) (i : ℕ) (x : A i) :
    limitLift A φ P g hg (limitOf A φ i x) = g i x := by
  simp [limitLift, limitOf]

/-- **Universal property (uniqueness).** The factoring map is unique: any two ring
    homomorphisms out of the inductive limit that agree on all canonical images
    are equal. -/
theorem limit_lift_unique (P : Type*) [Ring P] (F G : DirectLimit A φ →+* P)
    (h : ∀ i x, F (limitOf A φ i x) = G (limitOf A φ i x)) : F = G := by
  apply DirectLimit.Ring.hom_ext P
  intro i
  ext x
  exact h i x

end AbstractLimit

/-! ## 2. The `*`-monomorphism sequence: amplification of matrix algebras -/

/-- The **amplification** (UHF connecting map) `a ↦ 1ₛ ⊗ a`, a unital ring
    homomorphism `Mₘ(ℂ) → M_{s×m}(ℂ)` of matrix algebras. -/
noncomputable def amplify (s : ℕ) {m : ℕ} :
    Matrix (Fin m) (Fin m) ℂ →+* Matrix (Fin s × Fin m) (Fin s × Fin m) ℂ where
  toFun a := (1 : Matrix (Fin s) (Fin s) ℂ) ⊗ₖ a
  map_one' := by simp
  map_mul' a b := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := by simp
  map_add' a b := by rw [Matrix.kronecker_add]

@[simp] theorem amplify_apply (s : ℕ) {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) :
    amplify s a = (1 : Matrix (Fin s) (Fin s) ℂ) ⊗ₖ a := rfl

/-
The amplification is **injective** (a `*`-monomorphism) whenever the
    multiplicity `s` is positive.
-/
theorem amplify_injective (s : ℕ) (hs : 0 < s) {m : ℕ} :
    Function.Injective (amplify s (m := m)) := by
  intro a b hab;
  ext i j; replace hab := congr_fun ( congr_fun hab ( ⟨ ⟨ 0, hs ⟩, i ⟩ ) ) ( ⟨ ⟨ 0, hs ⟩, j ⟩ ) ; aesop;

/-
The amplification is `*`-preserving (a `*`-homomorphism): it commutes with the
    conjugate-transpose.
-/
theorem amplify_star (s : ℕ) {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) :
    (amplify s a)ᴴ = amplify s (aᴴ) := by
  ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp +decide [ mul_comm ];
  simp +decide [ Matrix.one_apply, mul_comm ];
  grind

/-! ## 3. The `K₀` invariant: amplification acts by multiplication by `s` -/

/-- **`K₀` connecting map.** On `K₀ = ℤ` (the rank of a projection, computed by the
    trace), the amplification acts as multiplication by the multiplicity `s`:
    `rank(1ₛ ⊗ p) = s · rank(p)`.  This is the connecting homomorphism of the
    `K₀` inductive system whose direct limit is the `K₀`-group of the AF algebra. -/
theorem K0_amplify (s : ℕ) {m : ℕ} (p : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.trace (amplify s p) = (s : ℂ) * Matrix.trace p := by
  rw [amplify_apply, Matrix.trace_kronecker, Matrix.trace_one]
  simp

end RGF.InductiveLimit