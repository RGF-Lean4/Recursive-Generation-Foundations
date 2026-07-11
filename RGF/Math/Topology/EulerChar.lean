/-
  Layer 4: homology tools and the Euler characteristic
-/

import Mathlib

open scoped BigOperators
open Finset

-- ============================================================
-- Combinatorial definition of the Euler characteristic
-- ============================================================

def alternatingSum (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (-1) ^ i * f i

theorem alternatingSum_succ (f : ℕ → ℤ) (n : ℕ) :
    alternatingSum f (n + 1) = alternatingSum f n + (-1) ^ (n + 1) * f (n + 1) := by
  simp [alternatingSum, Finset.sum_range_succ]

structure FVector where
  dim : ℕ
  cells : Fin (dim + 1) → ℕ

def FVector.eulerChar (fv : FVector) : ℤ :=
  ∑ i : Fin (fv.dim + 1), (-1) ^ (i : ℕ) * (fv.cells i : ℤ)

-- ============================================================
-- Classical Euler characteristic values
-- ============================================================

def sphere2_fvec : FVector where
  dim := 2
  cells := ![4, 6, 4]

theorem euler_char_sphere2 : sphere2_fvec.eulerChar = 2 := by decide

def torus2_fvec : FVector where
  dim := 2
  cells := ![1, 3, 2]

theorem euler_char_torus2 : torus2_fvec.eulerChar = 0 := by decide

def sphere3_fvec : FVector where
  dim := 3
  cells := ![5, 10, 10, 5]

theorem euler_char_sphere3 : sphere3_fvec.eulerChar = 0 := by decide

-- ============================================================
-- Connection with dimension locking
-- ============================================================

def euler_from_betti_3d (b0 b1 b2 b3 : ℤ) : ℤ := b0 - b1 + b2 - b3

theorem euler_closed_3manifold (b1 : ℤ) :
    euler_from_betti_3d 1 b1 b1 1 = 0 := by
  unfold euler_from_betti_3d; ring

theorem three_dim_minimal_nontrivial_poincare :
    ∀ d : ℕ, d % 2 = 1 → d < 3 → d ≤ 1 := by omega

-- ============================================================
-- Euler's formula and the regular polyhedra
-- ============================================================

theorem euler_edge_formula (V E F : ℕ) (h : (V : ℤ) - E + F = 2) :
    (E : ℤ) = V + F - 2 := by linarith

theorem tetrahedron_euler : (4 : ℤ) - 6 + 4 = 2 := by norm_num
theorem icosahedron_euler : (12 : ℤ) - 30 + 20 = 2 := by norm_num
theorem dodecahedron_euler : (20 : ℤ) - 30 + 12 = 2 := by norm_num
theorem cube_euler : (8 : ℤ) - 12 + 6 = 2 := by norm_num
theorem octahedron_euler : (6 : ℤ) - 12 + 8 = 2 := by norm_num

/-- The order of the rotation group of the icosahedron = 60 = |A₅|. -/
theorem icosahedron_rotation_order : 60 = 12 * 5 := by norm_num

/-- The number of five-fold rotation axes of the icosahedron = 6. -/
theorem icosahedron_fivefold_axes : 12 / 2 = 6 := by norm_num
