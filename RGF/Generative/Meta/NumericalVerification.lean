/-
  Computational verification module of recursive generation theory
  Lean support for Paper 16

  Uses #eval and decide for exhaustive / numerical verification of the core predictions
-/

import Mathlib

open Finset BigOperators

/-! ## 1. Exhaustive verification of quintic locking -/

/-- Spatial-closure condition C1. -/
def C1 (k : ℕ) : Bool := k ≥ 3

/-- Representation-theoretic stability condition C2. -/
def C2 (k : ℕ) : Bool :=
  if k % 2 = 1 then (k - 1) / 2 ≥ 2
  else (k - 2) / 2 ≥ 2

/-- Exhaustively check k = 1..20 for the smallest solution of C1 ∧ C2. -/
def findMinimalK (bound : ℕ) : Option ℕ :=
  (List.range bound).find? (fun k => C1 k && C2 k)

#eval findMinimalK 21  -- should yield some 5

/-- List all k ≤ 20 satisfying C1 ∧ C2. -/
def allSatisfyingK (bound : ℕ) : List ℕ :=
  (List.range bound).filter (fun k => C1 k && C2 k)

#eval allSatisfyingK 21  -- [5, 6, 7, 8, 9, 10, ...]

/-- Verify that k=5 is indeed the smallest. -/
theorem k5_minimal_computational :
    findMinimalK 21 = some 5 := by decide

/-! ## 2. Computational verification of Turán-graph edge counts -/

/-- The edge-count formula for the Turán graph T(n, r). -/
def turanEdges (n r : ℕ) : ℕ :=
  if r = 0 then 0
  else
    let q := n / r
    let s := n % r
    -- edge count = n²(r-1)/(2r) minus a correction term
    -- equivalent to the integer version of (1/2)(n² - s·(q+1)² - (r-s)·q²)
    (n * n - s * (q + 1) * (q + 1) - (r - s) * q * q) / 2

#eval turanEdges 6 3   -- T(6,3) = 12
#eval turanEdges 10 5  -- T(10,5) = 40
#eval turanEdges 9 3   -- T(9,3) = 27

/-- Verify T(6,3) = 12 (the edge count of the Turán graph K_{2,2,2}). -/
theorem turan_6_3 : turanEdges 6 3 = 12 := by decide

/-- Verify T(10,5) = 40. -/
theorem turan_10_5 : turanEdges 10 5 = 40 := by decide

/-! ## 3. Systematic search of the divisibility conditions for Steiner systems -/

/-- Check whether all divisibility conditions for S(t, k, v) are satisfied. -/
def steinerDivisibilityCheck (t k v : ℕ) : Bool :=
  (List.range t).all fun i =>
    let num := Nat.choose (v - i) (t - i)
    let den := Nat.choose (k - i) (t - i)
    den > 0 && num % den = 0

#eval steinerDivisibilityCheck 5 8 24  -- true
#eval steinerDivisibilityCheck 6 8 24  -- false
#eval steinerDivisibilityCheck 5 6 12  -- true (Steiner S(5,6,12))

/-- For a given t, search all possible (k, v) satisfying the divisibility conditions. -/
def searchSteiner (t : ℕ) (maxV : ℕ) : List (ℕ × ℕ) :=
  (List.range maxV).foldl (fun acc v =>
    let validK := (List.range v).filter (fun k =>
      k > t && steinerDivisibilityCheck t k (v + 1))
    acc ++ validK.map (fun k => (k + 1, v + 1))
  ) []

#eval searchSteiner 5 30  -- search for Steiner-system candidates with t=5

/-- Formal verification of the divisibility conditions for S(5,8,24). -/
theorem steiner_5_8_24_valid : steinerDivisibilityCheck 5 8 24 = true := by decide

/-- S(6,8,24) does not satisfy the divisibility conditions. -/
theorem steiner_6_8_24_invalid : steinerDivisibilityCheck 6 8 24 = false := by decide

/-! ## 4. Systematic computation of Euler's totient φ(k) -/

/-- Compute and list φ(k) for k = 1..30. -/
def totientTable (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).map (fun k => (k + 1, Nat.totient (k + 1)))

#eval totientTable 30

/-- Find the smallest odd prime satisfying φ(k) ≥ 4. -/
def minOddPrimeTotientGe4 (bound : ℕ) : Option ℕ :=
  (List.range bound).find? (fun k =>
    Nat.Prime (k + 2) && (k + 2) % 2 = 1 && Nat.totient (k + 2) ≥ 4)
  |>.map (· + 2)

#eval minOddPrimeTotientGe4 20  -- some 5

/-- k=5 is indeed the smallest odd prime satisfying φ(k) ≥ 4. -/
theorem five_min_odd_prime_totient_ge4 :
    minOddPrimeTotientGe4 20 = some 5 := by decide

/-! ## 5. A concrete numerical simulation of the dual-layer iteration system -/

/-- A simple dual-layer iteration system: iteration of a probability distribution over 3 atoms. -/
def simpleIterate (weights : List Float) (steps : ℕ) : List Float :=
  match steps with
  | 0 => weights
  | n + 1 =>
    let prev := simpleIterate weights n
    -- a simple feedback rule: at each step distribute the maximal probability evenly
    let total := prev.foldl (· + ·) 0.0
    if total == 0.0 then prev
    else prev.map (fun w => 0.3 * w + 0.7 * (total / prev.length.toFloat))

#eval simpleIterate [0.1, 0.3, 0.6] 0
#eval simpleIterate [0.1, 0.3, 0.6] 5
#eval simpleIterate [0.1, 0.3, 0.6] 20
-- should converge to the uniform distribution [1/3, 1/3, 1/3]

/-! ## 6. Exhaustive verification of the Euler characteristic of the regular polyhedra -/

/-- Regular-polyhedron data: (V, E, F). -/
def platoniSolids : List (String × ℕ × ℕ × ℕ) :=
  [("Tetrahedron", 4, 6, 4),
   ("Cube", 8, 12, 6),
   ("Octahedron", 6, 12, 8),
   ("Dodecahedron", 20, 30, 12),
   ("Icosahedron", 12, 30, 20)]

/-- Verify V - E + F = 2 for all regular polyhedra. -/
def checkAllEuler : Bool :=
  platoniSolids.all (fun (_, v, e, f) => v + f == e + 2)

#eval checkAllEuler  -- true

theorem all_platonic_euler : checkAllEuler = true := by decide
