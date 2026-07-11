/-
  RGF/StochasticPDEFRG.lean

  Direction I — Toward full continuum dynamics: rough paths and the functional
  (non-perturbative) renormalisation group.

  The existing RGF analysis layer works with "toy-limit" simplifications (e.g. the
  weakly-asymmetric reduction in the KPZ scaling law).  This module adds two
  pieces of genuine machinery pointing at the continuum theory:

  1. **Rough-path signature and Chen's identity.**  For a scalar driving path we
     define the depth-2 truncated signature and the truncated tensor product, and
     prove Chen's multiplicative property `S[s,u] ⊗ S[u,t] = S[s,t]`
     (`sig_chen`), the algebraic backbone of Lyons' rough-path / Hairer
     regularity-structure approach to SPDEs.  We also prove the truncated tensor
     product is a monoid (`chen_assoc`, `chen_one_mul`, `chen_mul_one`).

  2. **Wetterich functional-RG flow.**  We formalise the exact renormalisation-
     group flow of the effective average action as an operator equation on the
     (finite-dimensional regularised) field space: the flow generator is the
     "one-loop-exact" functional trace
     `𝓕(P, Ṙ) = ½ Tr(P · Ṙ)`, with `P = (Γ⁽²⁾ + R)⁻¹` the full field-dependent
     propagator.  We prove it is linear in the regulator insertion `Ṙ`
     (`wetterich_add`, `wetterich_smul`), the defining propagator identity
     `(Γ⁽²⁾ + R) · P = 1` (`wetterich_propagator`), and the modewise (diagonal)
     reduction `𝓕 = ½ ∑ᵢ Pᵢᵢ Ṙᵢᵢ` (`wetterich_diagonal`) that turns the
     functional equation into the standard flow of the individual modes.

  Contents live in namespace `RGF.SPDE`.
-/
import Mathlib

open Finset BigOperators Matrix

namespace RGF.SPDE

/-! ## 1. Rough paths: depth-2 signature and Chen's identity -/

/-- The depth-2 truncated signature of a scalar increment `d = x_t − x_s`:
    the pair `(level-1, level-2) = (d, d²/2)`. -/
noncomputable def sig (d : ℝ) : ℝ × ℝ := (d, d ^ 2 / 2)

/-- Truncated (depth-2) tensor product on the scalar signature algebra
    `ℝ × ℝ`: `(a₁,a₂) ⊗ (b₁,b₂) = (a₁+b₁, a₂+b₂+a₁·b₁)`. -/
def chen (a b : ℝ × ℝ) : ℝ × ℝ := (a.1 + b.1, a.2 + b.2 + a.1 * b.1)

/-- The truncated tensor product is associative. -/
theorem chen_assoc (a b c : ℝ × ℝ) : chen (chen a b) c = chen a (chen b c) := by
  apply Prod.ext <;> simp only [chen] <;> ring

/-- Left identity for the truncated tensor product. -/
theorem chen_one_mul (a : ℝ × ℝ) : chen (0, 0) a = a := by
  apply Prod.ext <;> simp only [chen] <;> ring

/-- Right identity for the truncated tensor product. -/
theorem chen_mul_one (a : ℝ × ℝ) : chen a (0, 0) = a := by
  apply Prod.ext <;> simp only [chen] <;> ring

/-- **Chen's identity.** The signature is multiplicative under concatenation of
    increments: `S(d₁) ⊗ S(d₂) = S(d₁ + d₂)`.  This is the depth-2 case of the
    multiplicativity of the rough-path signature. -/
theorem sig_chen (d₁ d₂ : ℝ) : chen (sig d₁) (sig d₂) = sig (d₁ + d₂) := by
  apply Prod.ext
  · simp only [sig, chen]
  · simp only [sig, chen]; ring

/-! ## 2. Wetterich functional renormalisation-group flow -/

variable {n : ℕ}

/-- The Wetterich flow generator on the finite-dimensional regularised field
    space: `𝓕(P, Ṙ) = ½ Tr(P · Ṙ)`, where `P` is the full propagator (the
    inverse of `Γ⁽²⁾ + R`) and `Ṙ = ∂_t R` is the scale derivative of the
    regulator. -/
noncomputable def wetterich (P Rdot : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 2 : ℝ) * Matrix.trace (P * Rdot)

/-- The full field-dependent propagator `P = (Γ⁽²⁾ + R)⁻¹`. -/
noncomputable def propagator (Gamma2 R : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (Gamma2 + R)⁻¹

/-- Linearity of the flow generator in the regulator insertion `Ṙ`. -/
theorem wetterich_add (P Rdot₁ Rdot₂ : Matrix (Fin n) (Fin n) ℝ) :
    wetterich P (Rdot₁ + Rdot₂) = wetterich P Rdot₁ + wetterich P Rdot₂ := by
  simp only [wetterich, Matrix.trace_add, mul_add]

/-- Homogeneity of the flow generator in the regulator insertion. -/
theorem wetterich_smul (c : ℝ) (P Rdot : Matrix (Fin n) (Fin n) ℝ) :
    wetterich P (c • Rdot) = c * wetterich P Rdot := by
  simp only [wetterich, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]; ring

/-- **Propagator identity.** When `Γ⁽²⁾ + R` is invertible, the propagator
    satisfies `(Γ⁽²⁾ + R) · P = 1` — the defining relation of the full propagator
    appearing in the Wetterich equation. -/
theorem wetterich_propagator (Gamma2 R : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (Gamma2 + R).det) :
    (Gamma2 + R) * propagator Gamma2 R = 1 := by
  unfold propagator; exact Matrix.mul_nonsing_inv _ h

/-- **Modewise reduction.** For a diagonal propagator and a diagonal regulator
    insertion, the functional flow reduces to the sum of the individual mode
    contributions `½ ∑ᵢ Pᵢ Ṙᵢ` — the standard modewise Wetterich flow. -/
theorem wetterich_diagonal (p r : Fin n → ℝ) :
    wetterich (Matrix.diagonal p) (Matrix.diagonal r)
      = (1 / 2 : ℝ) * ∑ i, p i * r i := by
  simp only [wetterich, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

end RGF.SPDE
