/-
  Paper 5 (+ 5S) — "Part V: d=3 and the self-consistency of the Z5 chiral structure"
  (d=3 and the self-consistency of the Z5 chiral structure), L. Sun 2026.

  Placed in the RGF `Math/Algebra` layer.  Formalizes the paper's arithmetic
  backbone connecting the two independent `d = 3` derivations:

  * self-dual algebraic path (§ from Paper 3): `dim so(d) = d(d−1)/2`, and the
    self-duality condition `dim so(d) = d` selects `d = 3` uniquely (for `d ≥ 1`);
  * chirality path (§3): a nontrivial chiral action requires *even* emergent
    spacetime dimension `d+1`, i.e. *odd* space dimension `d`;
  * confluence (§4): odd `d` with `dim so(d) = d` forces `d = 3`;
  * minimality (§5, 5S §SM-01): the complex Clifford/spinor dimensions
    `dim_ℂ Cliff_ℂ(d) = 2^d` and `dim_ℂ S = 2^{⌊d/2⌋}`; at `d = 3` the spinor
    dimension is `2` (matching `Cliff_ℂ(3) ≅ Mat₂(ℂ)`), while odd `d > 3` give
    strictly larger, redundant spinor dimensions.
-/
import Mathlib

namespace RGF.Paper5

/-- Dimension of the rotation algebra `so(d) = d(d−1)/2`. -/
def soDim (d : ℕ) : ℕ := d * (d - 1) / 2

/-- Complex dimension of the Clifford algebra `Cliff_ℂ(d) = 2^d`. -/
def cliffComplexDim (d : ℕ) : ℕ := 2 ^ d

/-- Complex dimension of the irreducible spinor representation `2^{⌊d/2⌋}`. -/
def spinorComplexDim (d : ℕ) : ℕ := 2 ^ (d / 2)

/-- `dim so(3) = 3`. -/
theorem soDim_three : soDim 3 = 3 := by decide

/-
Self-dual selection: for `d ≥ 1`, the algebraic self-duality condition
`dim so(d) = d` holds iff `d = 3`.
-/
theorem soDim_selfdual (d : ℕ) (hd : 1 ≤ d) : soDim d = d ↔ d = 3 := by
  rcases d with ( _ | _ | _ | _ | _ | d ) <;> simp_all +arith +decide [ soDim ];
  exact Nat.ne_of_gt <| Nat.le_div_iff_mul_le zero_lt_two |>.2 <| by nlinarith;

/-
Chirality parity: the emergent spacetime dimension `d+1` is even iff the
space dimension `d` is odd.
-/
theorem chirality_even_spacetime (d : ℕ) : Even (d + 1) ↔ Odd d := by
  grind

/-
Confluence (§4): an odd space dimension satisfying the self-duality
condition `dim so(d) = d` must be exactly `d = 3`.
-/
theorem confluence_d3 (d : ℕ) (hodd : Odd d) (hself : soDim d = d) : d = 3 := by
  exact ( soDim_selfdual d hodd.pos ).mp hself

/-- At `d = 3` the complex Clifford dimension is `2^3 = 8` and the spinor
dimension is `2` (i.e. `Cliff_ℂ(3) ≅ ℂ⁴ = Mat₂(ℂ)/…` acts on a 2-dim spinor). -/
theorem clifford_spinor_three : cliffComplexDim 3 = 8 ∧ spinorComplexDim 3 = 2 := by
  decide

/-
Minimality (§5): among odd space dimensions `d ≥ 5`, the spinor dimension
strictly exceeds the `d = 3` value `2`, introducing redundant chiral
degrees of freedom.
-/
theorem spinor_redundant_above_three (d : ℕ) (hd : 5 ≤ d) :
    2 < spinorComplexDim d := by
  exact lt_of_lt_of_le ( by decide ) ( pow_le_pow_right₀ ( by decide ) ( show d / 2 ≥ 2 by omega ) )

end RGF.Paper5