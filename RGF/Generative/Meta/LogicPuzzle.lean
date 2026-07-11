import Mathlib

/-!
# Logic puzzle (knights and knaves) — with a machine-verified unique solution

**Problem.**
On an island every inhabitant is either a **knight** (who always tells the truth)
or a **knave** (who always lies). Three people A, B, C each make a statement:

* A says: "B is a knave."
* B says: "A and C are of the same kind (both knights or both knaves)."
* C says: "A is a knight."

**Question: what kind is each of A, B, C?**

---

**Solution (reasoning).**
Let `a, b, c : Bool`, where `true` denotes a knight and `false` a knave.
"Person X is a knight" holds iff "X's statement is true", so the three statements
translate to:

* A: `a = !b` (A is a knight ⇔ "B is a knave" is true ⇔ `b = false`);
* B: `b = (a == c)` (B is a knight ⇔ A and C are of the same kind);
* C: `c = a` (C is a knight ⇔ A is a knight).

From C we get `c = a`, so `a == c` is always true; substituting into B gives
`b = true` (B is a knight). Substituting into A gives `a = !true = false`
(A is a knave); finally `c = a` gives `c = false` (C is a knave).

**Answer: A is a knave, B is a knight, C is a knave.** This solution is unique
(verified by `puzzle_unique` below).
-/

namespace RGF.LogicPuzzle

/-- **Uniqueness**: the only assignment satisfying the three statements is
    `A = knave, B = knight, C = knave`.
    (`true` = knight, `false` = knave.) -/
theorem puzzle_unique (a b c : Bool)
    (hA : a = !b) (hB : b = (a == c)) (hC : c = a) :
    a = false ∧ b = true ∧ c = false := by
  revert hA hB hC; revert a b c; decide

/-- **Existence**: the answer above does simultaneously satisfy the three statements. -/
theorem puzzle_solution :
    (false = !true) ∧ (true = (false == false)) ∧ (false = false) := by decide

end RGF.LogicPuzzle
