/-
  RGF2/Hierarchy/Reflection.lean   (module `RGF2.Hierarchy.Reflection`)
  — layer 1: the Montague–Lévy reflection principle for the RGF 2.0 hierarchy.

  **RGF 2.0 — Path 2, strengthened: a genuine (Montague–Lévy) reflection
  principle.**

  `RGF2/Hierarchy/Cumulative.lean` already records a weak reflection statement
  (`Vhier_reflection`): every set together with its members fits into a single
  stage `V_o`.  That is really just transitivity of the stages.

  The *Montague–Lévy* reflection theorem is much stronger: the cumulative hierarchy
  reflects arbitrary first-order properties.  In its Skolem/closure form — the
  engine driving the schema, since the Skolem functions of a first-order formula
  are class functions `ZFSet → ZFSet` — it states that for **any** class function
  and **any** ordinal there are arbitrarily large *limit* stages `V_α` that are
  closed under it.  Iterating over the finitely many Skolem functions of a formula
  then yields the usual reflection of that formula between `V_α` and the universe.

  This file proves that closure form, first for the ambient von Neumann hierarchy
  (`vonNeumann_reflection`) and then transported to the RGF 2.0 universe:

    * `vonNeumann_reflection`     for every `F : ZFSet → ZFSet` and ordinal `β`
                                  there is a limit ordinal `α > β` with `V_α` closed
                                  under `F`;
    * `Vhier_reflection_strong`   the same for the RGF 2.0 hierarchy `Vhier` and any
                                  internal class function `f : RGFSet₂ → RGFSet₂`;
    * `Vhier_reflection_pair`     the two-function version (closure under a pair of
                                  class functions simultaneously), illustrating the
                                  finite-family form used to reflect a whole formula.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Core.WType
import RGF.Math.SetTheory.RGF2.Hierarchy.Cumulative

open ZFSet Ordinal

universe u

namespace RGF
namespace RGF2

/-
**Montague–Lévy reflection (closure form), ambient version.**  For any class
function `F : ZFSet → ZFSet` and any ordinal `β`, there is a limit ordinal `α > β`
such that the von Neumann stage `V_α` is closed under `F`.
-/
theorem vonNeumann_reflection (F : ZFSet.{u} → ZFSet.{u}) (β : Ordinal.{u}) :
    ∃ α, β < α ∧ Order.IsSuccLimit α ∧ ∀ x ∈ V_ α, F x ∈ V_ α := by
  haveI : ZFSet.Definable₁ F := Classical.allZFSetDefinable ( fun v => F ( v 0 ) );
  -- Define a strictly increasing chain γ : ℕ → Ordinal by γ 0 = Order.succ β and γ (k+1) = max (Order.succ (γ k)) (Order.succ ((ZFSet.image F (V_ (γ k))).rank)).
  set γ : ℕ → Ordinal := fun k => Nat.recOn k (Order.succ β) (fun k γk => max (Order.succ γk) (Order.succ (rank (ZFSet.image F (V_ γk)))) );
  -- Let α = ⨆ k, γ k (the iSup of a ℕ-indexed family of ordinals; use Ordinal.le_iSup / Ordinal.iSup_le).
  set α : Ordinal := ⨆ k, γ k;
  refine' ⟨ α, _, _, _ ⟩;
  · refine' lt_of_lt_of_le _ ( Ordinal.le_iSup _ 0 );
    exact Order.lt_succ β;
  · refine' ⟨ _, _ ⟩;
    · simp +zetaDelta at *;
      refine' ne_of_gt ( lt_of_lt_of_le _ ( Ordinal.le_iSup _ 0 ) );
      exact Ordinal.succ_pos _;
    · intro x hx;
      obtain ⟨ k, hk ⟩ := hx;
      contrapose! hk;
      obtain ⟨ k, hk ⟩ := exists_lt_of_lt_ciSup k;
      exact ⟨ γ k, hk, lt_of_lt_of_le ( show γ k < γ ( k + 1 ) from lt_max_of_lt_left ( Order.lt_succ _ ) ) ( le_ciSup ( Ordinal.bddAbove_of_small _ ) _ ) ⟩;
  · intro x hx
    obtain ⟨k, hk⟩ : ∃ k, rank x < γ k := by
      contrapose! hx;
      rw [ ZFSet.mem_vonNeumann ];
      exact not_lt_of_ge ( Ordinal.iSup_le hx );
    -- Since x ∈ V_ (γ k), we have F x ∈ ZFSet.image F (V_ (γ k)).
    have hF_x_image : F x ∈ ZFSet.image F (V_ (γ k)) := by
      exact ZFSet.mem_image.2 ⟨ x, by simpa using ZFSet.mem_vonNeumann.2 hk, rfl ⟩;
    -- Since (F x).rank < γ (k+1) ≤ α, we have F x ∈ V_ α.
    have hF_x_rank : (F x).rank < α := by
      have hF_x_rank : (F x).rank < γ (k + 1) := by
        exact lt_of_lt_of_le ( ZFSet.rank_lt_of_mem hF_x_image ) ( le_max_of_le_right ( le_of_lt ( Order.lt_succ _ ) ) );
      exact lt_of_lt_of_le hF_x_rank ( Ordinal.le_iSup _ _ );
    grind +suggestions

/-- **Montague–Lévy reflection for the RGF 2.0 hierarchy.**  For any internal class
function `f : RGFSet₂ → RGFSet₂` and any ordinal `β`, there is a limit ordinal
`α > β` such that the RGF 2.0 stage `Vhier α` is closed under `f`. -/
theorem Vhier_reflection_strong (f : RGFSet₂.{u} → RGFSet₂.{u}) (β : Ordinal.{u}) :
    ∃ α, β < α ∧ Order.IsSuccLimit α ∧
      ∀ x, Mem₂ x (Vhier α) → Mem₂ (f x) (Vhier α) := by
  classical
  set F : ZFSet.{u} → ZFSet.{u} := fun v => equivZF (f (equivZF.symm v)) with hF
  obtain ⟨α, hβ, hlim, hclosed⟩ := vonNeumann_reflection F β
  refine ⟨α, hβ, hlim, ?_⟩
  intro x hx
  have hxZ : equivZF x ∈ V_ α := by
    rw [mem_Vhier_iff, rank₂] at hx; rwa [ZFSet.mem_vonNeumann]
  have := hclosed (equivZF x) hxZ
  rw [hF] at this
  simp only [Equiv.symm_apply_apply] at this
  rw [mem_Vhier_iff, rank₂]
  rwa [ZFSet.mem_vonNeumann] at this

/-- **Two-function (finite-family) reflection.**  For any two internal class
functions and any ordinal `β`, there is a limit stage `Vhier α`, `α > β`, closed
under both — the shape one uses to reflect a formula with several Skolem functions. -/
theorem Vhier_reflection_pair (f g : RGFSet₂.{u} → RGFSet₂.{u}) (β : Ordinal.{u}) :
    ∃ α, β < α ∧ Order.IsSuccLimit α ∧
      (∀ x, Mem₂ x (Vhier α) → Mem₂ (f x) (Vhier α)) ∧
      (∀ x, Mem₂ x (Vhier α) → Mem₂ (g x) (Vhier α)) := by
  -- Reflect the single class function `x ↦ {f x, g x}`; a stage closed under it
  -- is closed under both `f` and `g` because the stages are transitive.
  obtain ⟨α, hβ, hlim, hclosed⟩ :=
    Vhier_reflection_strong (fun x => pair₂ (f x) (g x)) β
  refine ⟨α, hβ, hlim, ?_, ?_⟩
  · intro x hx
    have hpair := hclosed x hx
    exact Vhier_transitive α _ (f x) hpair ((mem_pair₂ (f x) (g x) (f x)).2 (Or.inl rfl))
  · intro x hx
    have hpair := hclosed x hx
    exact Vhier_transitive α _ (g x) hpair ((mem_pair₂ (f x) (g x) (g x)).2 (Or.inr rfl))

end RGF2
end RGF