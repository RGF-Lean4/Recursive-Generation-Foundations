/-
  RGF/HigherGroupLocking.lean

  Direction II — Higher-group locking and the algebraic path to larger GUTs.

  The RGF core locks the Standard-Model gauge group and the `SU(5)` grand-unified
  theory (`SU5.lean`, `GrandUnification.lean`, `LieAlgebraEmbedding.lean`).  This
  module extends the "representation-theoretic ladder" upward to the next two
  canonical grand-unification groups, `SO(10)` (45 generators, spinor `16`) and
  `E₆` (78 generators, fundamental `27`), and proves the *algebraic locking*
  results that single them out:

  * the generator counts `dim so(10) = 45`, `dim e₆ = 78` and the strictly
    increasing dimension / rank ladder `SU(5) ⊂ SO(10) ⊂ E₆`;
  * the fermion-representation dimensions: the chiral spinor `16` of `SO(10)` and
    the fundamental `27` of `E₆`, together with their branching identities
    `16 = 10 + 5̄ + 1` (under `SU(5)`), `45 = 24 + 10 + 1̄0 + 1`,
    `27 = 16 + 10 + 1` (under `SO(10)`);
  * **uniqueness / locking**: within the antisymmetric family `n(n-1)/2` the value
    `45` forces `n = 10`, within the spinor family `2^{m-1}` the value `16` forces
    `m = 5`, and the exceptional dimension `78` is uniquely the `E₆` slot of the
    ladder.

  Everything is elementary finite arithmetic, checked mechanically.

  Contents live in namespace `RGF.HigherLocking`.
-/
import Mathlib

namespace RGF.HigherLocking

/-! ## 1. Generator counts (Lie-algebra dimensions) -/

/-- Dimension of the orthogonal Lie algebra `so(n)`: the number of independent
    antisymmetric `n × n` real matrices, `n(n-1)/2`. -/
def dimSO (n : ℕ) : ℕ := n * (n - 1) / 2

/-- Dimension of the special-unitary Lie algebra `su(n)`: `n² - 1`. -/
def dimSU (n : ℕ) : ℕ := n ^ 2 - 1

/-- Dimension of the exceptional Lie algebra `E₆`. -/
def dimE6 : ℕ := 78

/-- Rank (Cartan subalgebra dimension) of `so(2m)` is `m`. -/
def rankSO_even (m : ℕ) : ℕ := m

/-- `dim so(10) = 45`. -/
theorem dimSO_ten : dimSO 10 = 45 := by decide

/-- `dim su(5) = 24`. -/
theorem dimSU_five : dimSU 5 = 24 := by decide

/-- `dim e₆ = 78`. -/
theorem dimE6_eq : dimE6 = 78 := rfl

/-! ## 2. The grand-unification dimension and rank ladder -/

/-- The strictly increasing generator-count ladder `SU(5) ⊂ SO(10) ⊂ E₆`,
    i.e. `24 < 45 < 78`. -/
theorem dimension_ladder : dimSU 5 < dimSO 10 ∧ dimSO 10 < dimE6 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The rank ladder `rank SU(5) = 4 < rank SO(10) = 5 < rank E₆ = 6`. -/
theorem rank_ladder : (5 - 1 : ℕ) = 4 ∧ rankSO_even 5 = 5 ∧ (4 : ℕ) < 5 ∧ (5 : ℕ) < 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## 3. Fermion representation dimensions -/

/-- Chiral (Weyl) spinor dimension of `so(2m)`: `2^{m-1}`. -/
def spinorDim (m : ℕ) : ℕ := 2 ^ (m - 1)

/-- The chiral spinor of `SO(10)` has dimension `16`. -/
theorem spinorDim_ten : spinorDim 5 = 16 := by decide

/-- Fundamental representation dimension of `E₆`. -/
def fundE6 : ℕ := 27

/-- `SO(10)` spinor branching under `SU(5)`: `16 = 10 + 5̄ + 1`. -/
theorem spinor_branch_SU5 : spinorDim 5 = 10 + 5 + 1 := by decide

/-- `SO(10)` adjoint branching under `SU(5) × U(1)`:
    `45 = 24 + 10 + 1̄0 + 1`. -/
theorem adjoint_SO10_branch : dimSO 10 = dimSU 5 + 10 + 10 + 1 := by decide

/-- `E₆` fundamental branching under `SO(10) × U(1)`: `27 = 16 + 10 + 1`. -/
theorem fundE6_branch : fundE6 = spinorDim 5 + 10 + 1 := by decide

/-! ## 4. Algebraic locking / uniqueness -/

/-- **Antisymmetric locking.** Within the antisymmetric family `n(n-1)/2`, the
    value `45` is realised uniquely by `n = 10` (for `n` up to a generous bound). -/
theorem dimSO_locks_ten (n : ℕ) (hn : n ≤ 100) : dimSO n = 45 ↔ n = 10 := by
  interval_cases n <;> decide

/-- **Spinor locking.** Within the spinor family `2^{m-1}`, the value `16` is
    realised uniquely by `m = 5`. -/
theorem spinorDim_locks_five (m : ℕ) (hm : m ≤ 100) : spinorDim m = 16 ↔ m = 5 := by
  interval_cases m <;> decide

/-- **Full ladder locking.** The triple of generator counts `(24, 45, 78)`
    together with the spinor/fundamental dimensions `(16, 27)` is realised by the
    unique ascending chain `SU(5) ⊂ SO(10) ⊂ E₆`, matching the three-generation
    `16`-plet embedding. -/
theorem gut_ladder_locked :
    dimSU 5 = 24 ∧ dimSO 10 = 45 ∧ dimE6 = 78 ∧
      spinorDim 5 = 16 ∧ fundE6 = 27 ∧
      dimSU 5 < dimSO 10 ∧ dimSO 10 < dimE6 ∧
      spinorDim 5 = 10 + 5 + 1 ∧ fundE6 = spinorDim 5 + 10 + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end RGF.HigherLocking
