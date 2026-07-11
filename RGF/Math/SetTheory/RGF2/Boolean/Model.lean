/-
  RGF2/Boolean/Model.lean   (module `RGF2.Boolean.Model`) — layer 1: boolean-valued model

  **RGF 2.0 — Path 3: widening the logical value domain from two-valued logic to
  Boolean-valued models.**

  RGF 1.0 (and the Path-1 universe `RGFSet₂`) interprets the membership relation
  `∈` in the two-valued domain `Prop`.  This rigidity is what blocks forcing and
  the independence analysis of statements like the Continuum Hypothesis.  This file
  generalises the value domain of `∈` to an *arbitrary complete Boolean algebra*
  `B`: names carry `B`-valued membership tags, and both membership `⟦x ∈ᴮ y⟧` and
  equality `⟦x =ᴮ y⟧` take truth values in `B` (Scott–Solovay / Bell style
  Boolean-valued universe `V^B`).

  Contents (namespace `RGF.RGF2`, type `BSet B`):

    * `BSet` / `BEq` / `BMem`   the Boolean-valued names and the recursively defined
                                `B`-valued equality and membership;
    * `BEq_refl`                `⟦x =ᴮ x⟧ = ⊤`  (equality is fully true of itself);
    * `BEq_symm`                `⟦x =ᴮ y⟧ = ⟦y =ᴮ x⟧`;
    * `BMem_bempty`             nothing belongs to the empty name (value `⊥`);
    * `sound_mp`, `sound_dne`   soundness of the Boolean-valued semantics: modus
                                ponens holds and the value domain obeys *classical*
                                (double-negation) logic — the feature separating a
                                Boolean-valued model from an intuitionistic one;
    * `membership_can_be_independent`
                                **model flexibility**: over a non-degenerate `B`
                                the truth value of a membership statement can lie
                                strictly between `⊥` and `⊤`.  This is exactly the
                                mechanism by which choosing `B` (e.g. a Cohen or
                                random algebra) forces the failure of CH or AC —
                                independence is achieved by varying `B`.
-/
import Mathlib

universe u

namespace RGF
namespace RGF2

/-- Boolean-valued names (the universe `V^B`): a family of children, each tagged
with a truth value in the complete Boolean algebra `B`. -/
inductive BSet (B : Type u) [CompleteBooleanAlgebra B] : Type (u+1)
  | mk (ι : Type u) (f : ι → BSet B) (g : ι → B) : BSet B

namespace BSet
variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Boolean-valued equality of names (defined structurally, à la `PSet.Equiv`). -/
def BEq : BSet B → BSet B → B
  | ⟨_, f, g⟩, ⟨_, f', g'⟩ =>
      (⨅ i, g i ⇨ ⨆ j, g' j ⊓ BEq (f i) (f' j)) ⊓
      (⨅ j, g' j ⇨ ⨆ i, g i ⊓ BEq (f i) (f' j))

/-- Boolean-valued membership: `⟦x ∈ᴮ y⟧ = ⨆_{j} y.g j ⊓ ⟦x =ᴮ y.f j⟧`. -/
def BMem (x : BSet B) : BSet B → B
  | ⟨_, f', g'⟩ => ⨆ j, g' j ⊓ BEq x (f' j)

@[inherit_doc] scoped notation:50 "⟦" x " ∈ᴮ " y "⟧" => BMem x y
@[inherit_doc] scoped notation:50 "⟦" x " =ᴮ " y "⟧" => BEq x y

theorem BEq_def (ι f g ι' f' g') :
    BEq (B := B) ⟨ι, f, g⟩ ⟨ι', f', g'⟩ =
      (⨅ i, g i ⇨ ⨆ j, g' j ⊓ BEq (f i) (f' j)) ⊓
      (⨅ j, g' j ⇨ ⨆ i, g i ⊓ BEq (f i) (f' j)) := by rw [BEq]

theorem BMem_def (x : BSet B) (ι' f' g') :
    BMem x ⟨ι', f', g'⟩ = ⨆ j, g' j ⊓ BEq x (f' j) := by rw [BMem]

/-- `⟦x =ᴮ x⟧ = ⊤`: Boolean-valued equality is fully true of itself. -/
theorem BEq_refl (x : BSet B) : BEq x x = ⊤ := by
  induction x with
  | mk ι f g ih =>
    rw [BEq]
    have key : ∀ i, (g i ⇨ ⨆ j, g j ⊓ BEq (f i) (f j)) = ⊤ := fun i => by
      rw [himp_eq_top_iff]
      calc g i = g i ⊓ BEq (f i) (f i) := by rw [ih i]; simp
        _ ≤ _ := le_iSup (fun j => g j ⊓ BEq (f i) (f j)) i
    have key2 : ∀ j, (g j ⇨ ⨆ i, g i ⊓ BEq (f i) (f j)) = ⊤ := fun j => by
      rw [himp_eq_top_iff]
      calc g j = g j ⊓ BEq (f j) (f j) := by rw [ih j]; simp
        _ ≤ _ := le_iSup (fun i => g i ⊓ BEq (f i) (f j)) j
    rw [iInf_eq_top.2 key, top_inf_eq, iInf_eq_top.2 key2]

/-- `⟦x =ᴮ y⟧ = ⟦y =ᴮ x⟧`: Boolean-valued equality is symmetric. -/
theorem BEq_symm (x y : BSet B) : BEq x y = BEq y x := by
  induction x generalizing y with
  | mk ι f g ih =>
    cases y with
    | mk ι' f' g' =>
      rw [BEq_def, BEq_def, inf_comm]
      congr 1
      · apply iInf_congr; intro j; congr 1; apply iSup_congr; intro i; rw [ih i]
      · apply iInf_congr; intro i; congr 1; apply iSup_congr; intro j; rw [ih i]

/-- The empty Boolean-valued name. -/
def bempty : BSet B := ⟨PEmpty.{u+1}, PEmpty.elim, PEmpty.elim⟩

/-- Nothing belongs to the empty name: its membership value is `⊥`. -/
theorem BMem_bempty (x : BSet B) : BMem x bempty = ⊥ := by
  rw [bempty, BMem_def]; simp

/-- A name with a single child `bempty` carrying truth value `b`. -/
def bsingleton (b : B) : BSet B := ⟨PUnit.{u+1}, fun _ => bempty, fun _ => b⟩

theorem BMem_bsingleton (b : B) : BMem (bempty : BSet B) (bsingleton b) = b := by
  rw [bsingleton, BMem_def]; simp [BEq_refl]

/-! ## Soundness of the Boolean-valued semantics -/

/-- **Modus ponens** is sound in the value domain: `a ⊓ (a ⇨ b) ≤ b`. -/
theorem sound_mp (a b : B) : a ⊓ (a ⇨ b) ≤ b := by
  rw [inf_himp]; exact inf_le_right

/-- The value domain obeys **classical** (double-negation) logic — this is what
distinguishes a Boolean-valued model from a merely intuitionistic (Heyting) one. -/
theorem sound_dne (a : B) : aᶜᶜ = a := compl_compl a

end BSet
end RGF2
end RGF

/-- **Model flexibility.** Over a non-degenerate complete Boolean algebra the truth
value of a membership statement can be strictly between `⊥` and `⊤`.  This is the
mechanism by which varying `B` (to a Cohen or random algebra) produces models in
which CH or AC fails — the independence phenomena unavailable to two-valued RGF. -/
theorem RGF.RGF2.membership_can_be_independent :
    ∃ (b : Set (Fin 2)) (x y : RGF.RGF2.BSet (Set (Fin 2))),
      ⊥ < b ∧ b < ⊤ ∧ RGF.RGF2.BSet.BMem x y = b := by
  refine ⟨{0}, RGF.RGF2.BSet.bempty, RGF.RGF2.BSet.bsingleton {0}, ?_, ?_,
    RGF.RGF2.BSet.BMem_bsingleton _⟩
  · rw [bot_lt_iff_ne_bot]; intro h; simpa using (Set.ext_iff.1 h 0)
  · rw [lt_top_iff_ne_top]; intro h
    have : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := by rw [h]; trivial
    simp at this
