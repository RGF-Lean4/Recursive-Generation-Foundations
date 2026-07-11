/-
  Paper — "String emergence and the dynamical origin of the graviton in RCD de-locking phase transitions"
  (Non-perturbative topological string emergence in recursive-constitutive
  de-locking phase transitions), L. Sun 2026.

  Placed in the RGF **Physics** layer (Layer 3 / Physics dynamics).

  Formalizes cleanly-statable cores of the emergence chain from discrete lattice
  dynamics to worldsheet string physics:

  * **critical dimension `D = 10`**: the total superstring worldsheet central
    charge `c(D) = 3D/2 − 15` vanishes iff `D = 10`;
  * **`ℤ₅` orbifold twisted sectors**: the four twisted-sector ground-state
    energies `L₀^{(k)} = k²/(2·25)` sum to `3/5`;
  * **graviton multiplet**: the first excited closed-string level
    `8ᵥ ⊗ 8ᵥ = 35 ⊕ 28 ⊕ 1` (graviton ⊕ Kalb–Ramond ⊕ dilaton), `35+28+1 = 8·8`;
  * **Doeblin geometric ergodicity**: a `(1−ε)`-total-variation contraction gives
    geometric decay `aₙ ≤ (1−ε)ⁿ a₀`;
  * **Gelfand–Fuks / Virasoro 2-cocycle** `ω(m,n) = (m³−m)` on the diagonal
    `m+n=0` is antisymmetric.
-/
import Mathlib

namespace RGF.PaperString

/-- Total superstring worldsheet central charge `c(D) = 3D/2 − 15`
(coordinates `+D`, worldsheet fermions `+D/2`, conformal ghosts `−26`,
superconformal ghosts `+11`). -/
def cTotal (D : ℕ) : ℚ := (3 : ℚ) / 2 * D - 15

/-- Weyl anomaly cancels iff `D = 10` (for `D > 0`). -/
theorem cTotal_zero_iff_ten (D : ℕ) (hD : 0 < D) : cTotal D = 0 ↔ D = 10 := by
  unfold cTotal
  constructor
  · intro h
    have : (D : ℚ) = 10 := by linarith
    exact_mod_cast this
  · rintro rfl; norm_num

/-- `ℤ₅` orbifold twisted-sector ground-state energy
`L₀^{(k)} = k²/(2·25)`, `k = 1,2,3,4` (indexed by `Fin 4` via `k.val + 1`). -/
def z5Twisted (k : Fin 4) : ℚ := ((k.val + 1) ^ 2 : ℚ) / (2 * 25)

/-- The four `ℤ₅` twisted-sector ground energies sum to `3/5`. -/
theorem z5_twisted_sum : ∑ k, z5Twisted k = 3 / 5 := by
  rw [Fin.sum_univ_four]; norm_num [z5Twisted]

/-- First excited closed-string level `8ᵥ ⊗ 8ᵥ = 35 ⊕ 28 ⊕ 1`
(graviton ⊕ Kalb–Ramond ⊕ dilaton): `35 + 28 + 1 = 8 · 8`. -/
theorem graviton_decomposition : 35 + 28 + 1 = 8 * 8 := by norm_num

/-- Doeblin geometric ergodicity: a total-variation `(1−ε)`-contraction
`aₙ₊₁ ≤ (1−ε)·aₙ` (with `0 ≤ 1−ε`) gives geometric decay `aₙ ≤ (1−ε)ⁿ · a₀`. -/
theorem doeblin_geometric (ε : ℝ) (a : ℕ → ℝ) (hε : 0 ≤ 1 - ε)
    (h : ∀ n, a (n + 1) ≤ (1 - ε) * a n) (n : ℕ) :
    a n ≤ (1 - ε) ^ n * a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc a (n + 1) ≤ (1 - ε) * a n := h n
      _ ≤ (1 - ε) * ((1 - ε) ^ n * a 0) := by
            exact mul_le_mul_of_nonneg_left ih hε
      _ = (1 - ε) ^ (n + 1) * a 0 := by ring

/-- Gelfand–Fuks / Virasoro 2-cocycle `ω(m,n) = (m³ − m)` on the diagonal
`m + n = 0` (and `0` otherwise). -/
def viraCocycle (m n : ℤ) : ℚ := if m + n = 0 then ((m ^ 3 - m : ℤ) : ℚ) else 0

/-- Antisymmetry of the Virasoro 2-cocycle: `ω(m,n) = −ω(n,m)`. -/
theorem viraCocycle_antisymm (m n : ℤ) : viraCocycle m n = - viraCocycle n m := by
  unfold viraCocycle
  by_cases h : m + n = 0
  · have h' : n + m = 0 := by omega
    have hn : n = -m := by omega
    rw [if_pos h, if_pos h', hn]; push_cast; ring
  · have h' : ¬ n + m = 0 := by omega
    rw [if_neg h, if_neg h']; ring

end RGF.PaperString
