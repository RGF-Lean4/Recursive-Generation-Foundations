/-
  Layer 4: a category-theoretic framework for dual-layer iteration systems
-/

import Mathlib

-- ============================================================
-- Abstract dual-layer system
-- ============================================================

structure AbstractDualLayer (R E : Type) where
  generate : R → E
  modify : E → R

namespace AbstractDualLayer

def step {R E : Type} (sys : AbstractDualLayer R E) (r : R) : R :=
  sys.modify (sys.generate r)

def FixedPoint {R E : Type} (sys : AbstractDualLayer R E) (r : R) : Prop :=
  sys.step r = r

def iterateN {R E : Type} (sys : AbstractDualLayer R E) (r : R) : ℕ → R
  | 0 => r
  | n + 1 => sys.step (sys.iterateN r n)

theorem iterate_fixed {R E : Type} (sys : AbstractDualLayer R E)
    (r : R) (hfix : sys.FixedPoint r) : ∀ n : ℕ, sys.iterateN r n = r := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold iterateN
    rw [ih]
    exact hfix

theorem step_idempotent_at_fixed {R E : Type}
    (sys : AbstractDualLayer R E) (r : R) (h : sys.FixedPoint r) :
    sys.step (sys.step r) = sys.step r := by
  unfold FixedPoint at h; rw [h]; exact h

theorem iterate_two {R E : Type}
    (sys : AbstractDualLayer R E) (r : R) :
    sys.iterateN r 2 = sys.step (sys.step r) := rfl

end AbstractDualLayer

-- ============================================================
-- Metric dual-layer system and contraction maps
-- ============================================================

structure MetricDualLayer (R E : Type) extends AbstractDualLayer R E where
  dist : R → R → ℝ
  dist_nonneg : ∀ x y, 0 ≤ dist x y
  dist_eq_zero : ∀ x y, dist x y = 0 ↔ x = y
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

structure ContractingDualLayer (R E : Type) extends MetricDualLayer R E where
  contractConst : ℝ
  contract_lt_one : contractConst < 1
  contract_nonneg : 0 ≤ contractConst
  contracting : ∀ x y, dist (toAbstractDualLayer.step x) (toAbstractDualLayer.step y) ≤
    contractConst * dist x y

theorem ContractingDualLayer.fixedPoint_unique {R E : Type}
    (sys : ContractingDualLayer R E)
    (r₁ r₂ : R)
    (h₁ : sys.toAbstractDualLayer.FixedPoint r₁)
    (h₂ : sys.toAbstractDualLayer.FixedPoint r₂) : r₁ = r₂ := by
  rw [← sys.dist_eq_zero]
  by_contra h
  have hd : 0 < sys.dist r₁ r₂ := by
    cases' (sys.dist_nonneg r₁ r₂).lt_or_eq with hlt heq
    · exact hlt
    · exfalso; exact h heq.symm
  have key := sys.contracting r₁ r₂
  have h1 : sys.toAbstractDualLayer.step r₁ = r₁ := h₁
  have h2 : sys.toAbstractDualLayer.step r₂ = r₂ := h₂
  rw [h1, h2] at key
  have hlt := sys.contract_lt_one
  nlinarith

-- ============================================================
-- Iteration convergence theorem
-- ============================================================

theorem ContractingDualLayer.iterate_dist_decay {R E : Type}
    (sys : ContractingDualLayer R E)
    (x y : R) (n : ℕ) :
    sys.dist (sys.toAbstractDualLayer.iterateN x n) (sys.toAbstractDualLayer.iterateN y n) ≤
    sys.contractConst ^ n * sys.dist x y := by
  induction n with
  | zero => simp [AbstractDualLayer.iterateN]
  | succ n ih =>
    simp only [AbstractDualLayer.iterateN]
    calc sys.dist (sys.toAbstractDualLayer.step (sys.toAbstractDualLayer.iterateN x n))
                  (sys.toAbstractDualLayer.step (sys.toAbstractDualLayer.iterateN y n))
        ≤ sys.contractConst * sys.dist (sys.toAbstractDualLayer.iterateN x n)
                                        (sys.toAbstractDualLayer.iterateN y n) :=
          sys.contracting _ _
      _ ≤ sys.contractConst * (sys.contractConst ^ n * sys.dist x y) :=
          mul_le_mul_of_nonneg_left ih sys.contract_nonneg
      _ = sys.contractConst ^ (n + 1) * sys.dist x y := by ring
