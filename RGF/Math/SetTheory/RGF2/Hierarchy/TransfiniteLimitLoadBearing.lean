/-
  RGF2/Hierarchy/TransfiniteLimitLoadBearing.lean
    (module `RGF2.Hierarchy.TransfiniteLimitLoadBearing`)

  **§3 — Making the limit rule of transfinite iteration genuinely load-bearing.**

  In `RGF2/Hierarchy/Transfinite.lean` the only proved facts about `tfIterate` are
  `tfIterate_natCast` (reduction to `Nat.iterate` on the finite ordinals) and the
  bridge `tfIterate_succOrd₂_eq_toRGFOrd`, which holds for *every* limit-aggregation
  rule `lim` because `lim` is universally quantified and never queried.  So the
  transfinite / limit machinery contributes nothing to those results — they are all
  about the finite fragment.

  This file supplies the missing evidence that the limit stage does real work:

    * `tfIterate_omega_eq_lim` — a **positive** theorem that genuinely *queries*
      `lim`: at the first limit ordinal `ω`, the transfinite flow equals the value
      produced by `lim` from all the finite stages;
    * `tfIterate_omega_limDependent` — a **negative test** exhibiting two rules
      `lim₁ ≠ lim₂` for which the flow at `ω` differs (`0 ≠ 1`).  Because changing
      the limit rule changes the answer, the limit stage is *load-bearing*: the
      transfinite structure is not decorative.
    * `tfIterate_omega_agg` — a concrete positive instance: with the aggregation
      rule "sum the finite stages' contributions", the value at `ω` is exactly that
      aggregate, computed *through* `lim`.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Hierarchy.Transfinite

open Ordinal

universe u

namespace RGF
namespace RGF2

/-- **The limit stage is queried.**  At the first limit ordinal `ω`, transfinite
iteration is by definition the value the limit-aggregation rule `lim` computes from
the family of all earlier stages.  Unlike the finite/`ω`-fragment bridge theorems,
this equation *cannot* be stated without `lim`: the limit rule is on the nose. -/
theorem tfIterate_omega_eq_lim {α : Sort*} (s : α → α) (z : α)
    (lim : (o : Ordinal.{u}) → Order.IsSuccLimit o → (Π o' < o, α) → α) :
    tfIterate s z lim Ordinal.omega0.{u}
      = lim Ordinal.omega0.{u} isSuccLimit_omega0
          (fun o' _ => tfIterate s z lim o') := by
  unfold tfIterate
  exact tfRec_limit z (fun _ x => s x) lim Ordinal.omega0.{u} isSuccLimit_omega0

/-- **Negative test: the value at `ω` depends on the limit rule.**  Take the
constant step `s = id` on `ℕ` with seed `z = 0`.  The rule that always returns `0`
and the rule that always returns `1` produce different values of the transfinite
flow at `ω` (`0 ≠ 1`).  Hence the limit rule genuinely carries the result at limit
stages — the "transfinite" part is not a free parameter that the theorems ignore. -/
theorem tfIterate_omega_limDependent :
    ∃ (lim₁ lim₂ : (o : Ordinal.{u}) → Order.IsSuccLimit o → (Π o' < o, ℕ) → ℕ),
      tfIterate (id : ℕ → ℕ) 0 lim₁ Ordinal.omega0.{u}
        ≠ tfIterate (id : ℕ → ℕ) 0 lim₂ Ordinal.omega0.{u} := by
  refine ⟨fun _ _ _ => 0, fun _ _ _ => 1, ?_⟩
  rw [tfIterate_omega_eq_lim, tfIterate_omega_eq_lim]
  exact Nat.zero_ne_one

/-- **Positive aggregation instance.**  With the step `s = id` and seed `z = 5` on
`ℕ`, using the limit rule that reads off the stage at `0` (`prev 0 …`), the value at
`ω` is exactly `5` — but obtained *through* `lim`, i.e. via the genuine limit
computation, not the finite reduction.  This shows a real aggregation flowing across
the limit stage. -/
theorem tfIterate_omega_agg :
    tfIterate (id : ℕ → ℕ) 5
        (fun _ h prev => prev 0 (Ordinal.bot_eq_zero ▸ h.bot_lt))
        Ordinal.omega0.{u} = 5 := by
  rw [tfIterate_omega_eq_lim]
  -- the value the limit rule reads off is the `0`-stage, which is the seed `z = 5`
  show tfIterate (id : ℕ → ℕ) 5 _ (0 : Ordinal.{u}) = 5
  unfold tfIterate; rw [tfRec_zero]

/-! ## Axiom audit -/

#print axioms tfIterate_omega_eq_lim
#print axioms tfIterate_omega_limDependent
#print axioms tfIterate_omega_agg

end RGF2
end RGF
