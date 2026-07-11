/-
  RGF2/Hierarchy/Transfinite.lean   (module `RGF2.Hierarchy.Transfinite`) — layer 1: transfinite recursion

  **RGF 2.0 — Path 4: internalising transfinite recursion and the well-ordering /
  Hartogs / choice machinery into the generative operator.**

  RGF 1.0 iterates its generative step along the *discrete* natural-number time
  axis (`iterate : ℕ → R → R`) or, at best, the real time axis, so the generation
  process is epistemologically capped at `ℵ₀` (or `2^ℵ₀`) many steps.  This file
  lifts the generative step to a **transfinite time flow**: the step is iterated
  along ordinal time via transfinite recursion, and the tools that make ordinal
  time non-trivial — the Hartogs "next size" function, the well-ordering theorem,
  and the axiom of choice — are recorded as genuine theorems.

  Contents (namespace `RGF.RGF2`):

    * `tfRec` / `tfRec_zero` / `tfRec_succ` / `tfRec_limit`
        transfinite recursion combinator with its defining equations at zero,
        successor and limit ordinals.
    * `tfIterate`
        transfinite iteration of a single generative step operator.
    * `tfIterate_natCast`
        on the finite ordinals the transfinite flow reduces *exactly* to ordinary
        `Nat.iterate`: the RGF 1.0 discrete flow is the restriction of the RGF 2.0
        transfinite flow.  (This is the "lossless replacement" of the iteration invariant.)
    * `hartogs` / `hartogs_no_inj`
        the internally generated Hartogs number: for every type there is an
        ordinal of strictly larger cardinality that does not inject into it — an
        unconditional "next cardinal" supplied by the transfinite dynamics.
    * `wellOrdering`
        the well-ordering theorem: every type carries a well-order.
    * `choiceFn`
        the axiom of choice as a non-trivial tool over arbitrary index families.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Core.WType

open Ordinal Cardinal

universe u

namespace RGF
namespace RGF2

/-! ## Transfinite recursion — the super-finite generative time flow -/

/-- Transfinite recursion combinator: data at zero (`z`), at successors (`s`) and
at limit ordinals (`lim`) determine a function on all of ordinal time. -/
noncomputable def tfRec {α : Sort*} (z : α) (s : Ordinal.{u} → α → α)
    (lim : (o : Ordinal.{u}) → Order.IsSuccLimit o → (Π o' < o, α) → α) : Ordinal.{u} → α :=
  fun o => Ordinal.limitRecOn o z s lim

@[simp] theorem tfRec_zero {α : Sort*} (z : α) s lim : tfRec z s lim 0 = z :=
  limitRecOn_zero _ _ _

theorem tfRec_succ {α : Sort*} (z : α) s lim (o : Ordinal.{u}) :
    tfRec z s lim (Order.succ o) = s o (tfRec z s lim o) :=
  limitRecOn_succ _ _ _ _

theorem tfRec_limit {α : Sort*} (z : α) s lim (o : Ordinal.{u}) (ho : Order.IsSuccLimit o) :
    tfRec z s lim o = lim o ho (fun o' _ => tfRec z s lim o') :=
  limitRecOn_limit _ _ _ _ ho

/-- Transfinite iteration of a single generative step operator `s`, starting from
`z`, with limit stages aggregated by `lim`. -/
noncomputable def tfIterate {α : Sort*} (s : α → α) (z : α)
    (lim : (o : Ordinal.{u}) → Order.IsSuccLimit o → (Π o' < o, α) → α) : Ordinal.{u} → α :=
  tfRec z (fun _ x => s x) lim

/-- **The RGF 1.0 discrete flow is the finite restriction of the RGF 2.0
transfinite flow.**  On the finite ordinals, transfinite iteration coincides with
ordinary `Nat.iterate`. -/
theorem tfIterate_natCast {α : Type*} (s : α → α) (z : α) lim (n : ℕ) :
    tfIterate s z lim (n : Ordinal.{u}) = s^[n] z := by
  induction n with
  | zero => rw [Nat.cast_zero, tfIterate, tfRec_zero]; rfl
  | succ k ih =>
    have hc : ((k + 1 : ℕ) : Ordinal.{u}) = Order.succ (k : Ordinal.{u}) := by
      rw [Nat.cast_succ, Ordinal.add_one_eq_succ]
    rw [tfIterate, hc, tfRec_succ]
    exact (congrArg s ih).trans (Function.iterate_succ_apply' s k z).symm

/-! ## Hartogs, well-ordering and choice -/

/-- **Hartogs.** For any type there is an ordinal of strictly larger cardinality —
the internally generated "next size". -/
theorem hartogs (α : Type u) : ∃ o : Ordinal.{u}, Cardinal.mk α < o.card := by
  refine ⟨(SuccOrder.succ (Cardinal.mk α)).ord, ?_⟩
  rw [card_ord]; exact Order.lt_succ _

/-- **Hartogs (no-injection form).** For any type there is an ordinal whose
underlying type does not inject into it. -/
theorem hartogs_no_inj (α : Type u) : ∃ o : Ordinal.{u}, ¬ Nonempty (o.ToType ↪ α) := by
  obtain ⟨o, ho⟩ := hartogs α
  refine ⟨o, ?_⟩
  rw [← Cardinal.le_def, mk_toType]; exact not_le.2 ho

/-- **Well-ordering theorem.** Every type carries a well-order — so transfinite
recursion applies to every set of the generative universe. -/
theorem wellOrdering (α : Type u) : ∃ r : α → α → Prop, IsWellOrder α r := by
  obtain ⟨_⟩ := exists_wellOrder α
  exact ⟨(· < ·), inferInstance⟩

/-- **Axiom of Choice** as a non-trivial tool: every family of non-empty types
admits a choice function, even over an infinite / transfinite index. -/
theorem choiceFn {ι : Type u} (X : ι → Type u) (h : ∀ i, Nonempty (X i)) :
    Nonempty (Π i, X i) := ⟨fun i => (h i).some⟩

end RGF2
end RGF
