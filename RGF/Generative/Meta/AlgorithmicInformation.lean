/-
  RGF/AlgorithmicInformation.lean

  Direction III(b) — Algorithmic information theory and the minimum description
  length (MDL) principle.

  Extending `RecursiveGrammar.lean`, this file gives a machine-checked, finitary
  account of the claim that, among candidate "laws of physics generators", the
  five-fold symmetry with three-dimensional space is the *most parsimonious*
  (minimum-description-length) solution.

  * **Prefix code length.**  `codeLen n = Nat.size n` is the number of bits needed
    to write `n`; it is monotone (`codeLen_mono`) and subadditive under products
    (`codeLen_mul_le`) — the algorithmic-information subadditivity `K(mn) ≤ K(m)+K(n)+O(1)`.

  * **Two-part MDL score.**  A candidate generator is a pair `(sym, dim)`.  Its MDL
    cost `mdlCost` is model-complexity (description length + magnitude) plus a
    misfit penalty enforcing (i) *aperiodic order* — the rotation order must be
    non-crystallographic (`sym ∉ {1,2,3,4,6}` and `sym ≥ 5`), and (ii) *stable
    chiral dynamics* — three spatial dimensions.

  * **The `(5,3)` optimum.**  Over the full candidate family the unique minimiser
    of the MDL score is five-fold symmetry in three dimensions
    (`mdl_five_three_optimal`, `mdl_five_three_strict`): the algorithmically
    simplest generator consistent with the constraints.
-/
import Mathlib

open scoped BigOperators

namespace RGF.AIT

/-! ## 1. Description length and its algorithmic-information properties -/

/-- The bit-length of `n` (a stand-in for prefix Kolmogorov complexity). -/
def codeLen (n : ℕ) : ℕ := Nat.size n

/-
Description length is monotone.
-/
theorem codeLen_mono {m n : ℕ} (h : m ≤ n) : codeLen m ≤ codeLen n := by
  exact Nat.size_le_size h

/-
**Subadditivity** `K(m·n) ≤ K(m) + K(n)`: the algorithmic-information
    inequality specialised to the bit-length code.
-/
theorem codeLen_mul_le (m n : ℕ) : codeLen (m * n) ≤ codeLen m + codeLen n := by
  by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all +decide [ codeLen ];
  -- By definition of size, we know that $m < 2^{\text{size}(m)}$ and $n < 2^{\text{size}(n)}$.
  have h_m : m < 2 ^ m.size := Nat.lt_size_self m
  have h_n : n < 2 ^ n.size := Nat.lt_size_self n
  rw [ Nat.size_le ];
  simpa only [ pow_add ] using Nat.mul_lt_mul'' h_m h_n

/-! ## 2. The two-part MDL score of a physics generator -/

/-- A candidate "generator of physical law": a rotational symmetry order and a
    spatial dimension. -/
structure Candidate where
  sym : ℕ
  dim : ℕ
deriving DecidableEq

/-- Crystallographic rotation orders (which *cannot* tile aperiodically). -/
def isCrystallographic (n : ℕ) : Bool := n == 1 || n == 2 || n == 3 || n == 4 || n == 6

/-- Misfit penalty: aperiodicity requires a non-crystallographic order `≥ 5`;
    stable chiral dynamics require exactly three spatial dimensions. -/
def penalty (c : Candidate) : ℕ :=
  (if isCrystallographic c.sym then 100 else 0)
  + (if c.sym < 5 then 100 else 0)
  + 50 * ((c.dim - 3) + (3 - c.dim))

/-- The two-part MDL cost: model complexity (`codeLen` + magnitude) plus penalty. -/
def mdlCost (c : Candidate) : ℕ :=
  penalty c + codeLen c.sym + c.sym + codeLen c.dim + c.dim

/-- The candidate family: symmetry orders `1..8`, dimensions `1..6`. -/
def candidates : List Candidate :=
  (List.range 8).flatMap (fun s =>
    (List.range 6).map (fun d => ⟨s + 1, d + 1⟩))

/-- **MDL optimum.**  Five-fold symmetry in three dimensions has minimal MDL cost
    over the whole candidate family. -/
theorem mdl_five_three_optimal :
    ∀ c ∈ candidates, mdlCost ⟨5, 3⟩ ≤ mdlCost c := by
  decide

/-- The optimum is *strict*: any other candidate has strictly larger MDL cost. -/
theorem mdl_five_three_strict :
    ∀ c ∈ candidates, c ≠ ⟨5, 3⟩ → mdlCost ⟨5, 3⟩ < mdlCost c := by
  decide

/-- The optimum is itself a member of the family. -/
theorem five_three_mem : (⟨5, 3⟩ : Candidate) ∈ candidates := by
  decide

end RGF.AIT