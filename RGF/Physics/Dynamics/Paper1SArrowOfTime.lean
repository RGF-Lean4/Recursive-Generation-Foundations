/-
  Paper 1S — "Supplementary material: Law as the inevitable emergence of change: the physical foundations of Recursive Constitutive Dynamics"
  (Supplement to Paper 1: the arrow of time and irreversibility of the
  locking-recovery rule), L. Sun 2026.

  Placed in the RGF **Physics** layer (Layer 3 / Physics dynamics).

  Formalizes the discrete arrow of time carried by the locking-recovery rule
  `r_{n+1}(x) = η_n(x)·(1 − η_{n+1}(x))` (§SM-01):

  * the recovery counter is **time-reversal asymmetric** — swapping the two
    time-adjacent occupation values changes it, so `T⁻¹ ∘ R_rec ∘ T ≠ R_rec`;
  * the **entropic arrow**: the family of reachable-state sets grows
    monotonically in time.
-/
import Mathlib

namespace RGF.Paper1S

/-- Locking-recovery counter `r = η_n·(1 − η_{n+1})`, on Boolean occupation
numbers `η ∈ {0,1}`. `recovery a b = true` iff the site was occupied at step `n`
(`a`) and vacated at step `n+1` (`b = false`). -/
def recovery (a b : Bool) : Bool := a && !b

/-- Time-reversal asymmetry (Prop. SM-01.1): swapping the two time-adjacent
occupation values changes the recovery counter, so the recovery rule is not
invariant under time reversal. -/
theorem recovery_time_asymmetric : ∃ a b : Bool, recovery a b ≠ recovery b a :=
  ⟨true, false, by decide⟩

/-- Entropic arrow (Prop. SM-01.2): if the reachable-state set can only grow at
each step, then it is monotone in time. -/
theorem reachable_monotone {X : Type*} (S : ℕ → Set X)
    (h : ∀ n, S n ⊆ S (n + 1)) : Monotone S :=
  monotone_nat_of_le_succ h

end RGF.Paper1S
