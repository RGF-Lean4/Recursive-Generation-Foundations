/-
  RGF2/Boolean/Forcing.lean   (module `RGF2.Boolean.Forcing`)
  — layer 1: forcing backbone for the RGF 2.0 Boolean-valued model.

  **RGF 2.0 — Path 3, strengthened: towards forcing and independence.**

  `RGF2/Boolean/Model.lean` set up the Boolean-valued universe `V^B = BSet B` over a
  complete Boolean algebra `B`, with `B`-valued equality `BEq` (reflexive and
  symmetric) and membership `BMem`, soundness of the value domain, and the basic
  *flexibility* result `membership_can_be_independent` (a membership value can lie
  strictly between `⊥` and `⊤`).

  This file continues formalising the forcing mechanism itself — the algebraic
  backbone that makes `V^B` a genuine Boolean-valued *model of set theory*:

    * `BEq_trans_le`         `⟦x =ᴮ y⟧ ⊓ ⟦y =ᴮ z⟧ ≤ ⟦x =ᴮ z⟧` — together with the
                             reflexivity/symmetry of `Model.lean` this makes `BEq` a
                             `B`-valued equivalence relation;
    * `BEq_mem_congr_left`   `⟦u =ᴮ v⟧ ⊓ ⟦u ∈ᴮ x⟧ ≤ ⟦v ∈ᴮ x⟧` (Leibniz on the left);
    * `BEq_mem_congr_right`  `⟦u =ᴮ v⟧ ⊓ ⟦x ∈ᴮ u⟧ ≤ ⟦x ∈ᴮ v⟧` (Leibniz on the right);
    * `bpair` / `BMem_bpair` / `forcing_pairing`
                             the Boolean-valued **pairing** operation `{x, y}ᴮ`, with
                             `⟦z ∈ᴮ {x,y}ᴮ⟧ = ⟦z =ᴮ x⟧ ⊔ ⟦z =ᴮ y⟧` — the pairing
                             axiom of ZFC validated in `V^B`;
    * `bmem_undecided`       **independence realised**: over a non-degenerate `B` there
                             is a membership statement `φ` with both `⟦φ⟧` and `⟦¬φ⟧`
                             nonzero — i.e. neither `φ` nor its negation is forced by
                             `⊤`.  This is exactly the shape of a forcing
                             independence result (varying `B` decides `φ` either way).

  Scope.  This is the *forcing backbone*, not yet a full independence proof of the
  Continuum Hypothesis or the Axiom of Choice: those require a specific forcing
  algebra (Cohen / random) and the evaluation of the corresponding statement's
  Boolean value, a substantially larger development.  What is proved here is that
  `V^B` genuinely behaves as a Boolean-valued model (equality is a congruence,
  pairing is validated) and that undecidedness is realised, which is the mechanism
  independence rests on.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Boolean.Model

universe u

namespace RGF
namespace RGF2
namespace BSet

variable {B : Type u} [CompleteBooleanAlgebra B]

/-
**Transitivity of `B`-valued equality.**  `⟦x =ᴮ y⟧ ⊓ ⟦y =ᴮ z⟧ ≤ ⟦x =ᴮ z⟧`.
-/
theorem BEq_trans_le (x y z : BSet B) : BEq x y ⊓ BEq y z ≤ BEq x z := by
  induction' x using BSet.recOn with ιx fx gx ihx generalizing y z;
  obtain ⟨ιy, fy, gy⟩ := y
  obtain ⟨ιz, fz, gz⟩ := z;
  refine' le_inf _ _;
  · refine' le_iInf _;
    intro i
    have h1 : gx i ⊓ (⟦mk ιx fx gx =ᴮ mk ιy fy gy⟧) ≤ ⨆ j, gy j ⊓ (⟦fx i =ᴮ fy j⟧) := by
      have h1 : gx i ⊓ (⟦mk ιx fx gx =ᴮ mk ιy fy gy⟧) ≤ gx i ⊓ (gx i ⇨ ⨆ j, gy j ⊓ (⟦fx i =ᴮ fy j⟧)) := by
        exact inf_le_inf_left _ ( inf_le_left.trans ( iInf_le _ i ) );
      exact h1.trans ( inf_himp_le );
    have h2 : ⨆ j, gy j ⊓ (⟦fx i =ᴮ fy j⟧) ⊓ (⟦mk ιy fy gy =ᴮ mk ιz fz gz⟧) ≤ ⨆ k, gz k ⊓ (⟦fx i =ᴮ fz k⟧) := by
      refine' iSup_le fun j => _;
      have h2 : gy j ⊓ (⟦mk ιy fy gy =ᴮ mk ιz fz gz⟧) ≤ ⨆ k, gz k ⊓ (⟦fy j =ᴮ fz k⟧) := by
        have h2 : (⟦mk ιy fy gy =ᴮ mk ιz fz gz⟧) ≤ ⨅ j, gy j ⇨ ⨆ k, gz k ⊓ (⟦fy j =ᴮ fz k⟧) := by
          exact inf_le_left;
        exact le_trans ( inf_le_inf_left _ ( h2.trans ( iInf_le _ j ) ) ) ( by simp +decide );
      refine' le_trans _ ( le_trans ( inf_le_inf_left _ h2 ) _ );
      rotate_left;
      exact ⟦fx i =ᴮ fy j⟧;
      · rw [ inf_iSup_eq ];
        refine' iSup_mono fun k => _;
        rw [ inf_comm ];
        rw [ inf_assoc ];
        exact inf_le_inf_left _ ( by simpa only [ inf_comm ] using ihx i ( fy j ) ( fz k ) );
      · simp +decide [ inf_assoc, inf_left_comm ];
    rw [ le_himp_iff ];
    refine' le_trans _ h2;
    convert inf_le_inf_right ( ⟦mk ιy fy gy =ᴮ mk ιz fz gz⟧ ) h1 using 1;
    · grind;
    · simp +decide [ inf_assoc, iSup_inf_eq ];
  · refine' le_iInf fun j => le_himp_iff.mpr _;
    have h_le : (⟦mk ιx fx gx =ᴮ mk ιy fy gy⟧) ⊓ (⟦mk ιy fy gy =ᴮ mk ιz fz gz⟧) ⊓ gz j ≤ ⨆ i, gx i ⊓ (BEq (fx i) (fz j)) := by
      have h_le' : (⟦mk ιy fy gy =ᴮ mk ιz fz gz⟧) ⊓ gz j ≤ ⨆ k, gy k ⊓ (BEq (fy k) (fz j)) := by
        have h_le' : (⟦mk ιy fy gy =ᴮ mk ιz fz gz⟧) ≤ ⨅ k, gz k ⇨ ⨆ i, gy i ⊓ (BEq (fy i) (fz k)) := by
          exact inf_le_right;
        refine' le_trans ( inf_le_inf_right _ h_le' ) _;
        exact le_trans ( inf_le_inf ( iInf_le _ j ) le_rfl ) ( by simp +decide )
      have h_le'' : (⟦mk ιx fx gx =ᴮ mk ιy fy gy⟧) ⊓ (⨆ k, gy k ⊓ (BEq (fy k) (fz j))) ≤ ⨆ i, gx i ⊓ (BEq (fx i) (fz j)) := by
        have h_le'' : (⟦mk ιx fx gx =ᴮ mk ιy fy gy⟧) ⊓ (⨆ k, gy k ⊓ (BEq (fy k) (fz j))) ≤ ⨆ k, (⟦mk ιx fx gx =ᴮ mk ιy fy gy⟧) ⊓ (gy k ⊓ (BEq (fy k) (fz j))) := by
          rw [ inf_iSup_eq ];
        refine' le_trans h_le'' ( iSup_le fun k => _ );
        have h_le''' : (⟦mk ιx fx gx =ᴮ mk ιy fy gy⟧) ⊓ gy k ≤ ⨆ i, gx i ⊓ (BEq (fx i) (fy k)) := by
          refine' le_trans ( inf_le_inf_right _ ( inf_le_right ) ) _;
          exact le_trans ( inf_le_inf_right _ ( iInf_le _ k ) ) ( by simp +decide );
        have h_le'''' : (⨆ i, gx i ⊓ (BEq (fx i) (fy k))) ⊓ (BEq (fy k) (fz j)) ≤ ⨆ i, gx i ⊓ (BEq (fx i) (fz j)) := by
          rw [ iSup_inf_eq ];
          exact iSup_mono fun i => by simpa only [ inf_assoc ] using inf_le_inf_left _ ( ihx i ( fy k ) ( fz j ) ) ;
        exact le_trans ( by rw [ ← inf_assoc ] ; exact inf_le_inf_right _ h_le''' ) h_le'''';
      exact le_trans ( by rw [ inf_assoc ] ; exact inf_le_inf_left _ h_le' ) h_le'';
    exact h_le

/-
**Leibniz congruence (right argument of `∈`).**
`⟦u =ᴮ v⟧ ⊓ ⟦x ∈ᴮ u⟧ ≤ ⟦x ∈ᴮ v⟧`.
-/
theorem BEq_mem_congr_right (u v x : BSet B) : BEq u v ⊓ BMem x u ≤ BMem x v := by
  -- By definition of $BSet.BEq$, we know that $⟦x =ᴮ v⟧ = (⨅ j, (v.g j) ⇨ ⨆ k, (v.g k) ⊓ BEq (v.f j) (v.f k)) ⊓ (⨅ k, (v.g k) ⇨ ⨆ j, (v.g j) ⊓ BEq (v.f j) (v.f k))$.
  obtain ⟨ιu, fu, gu⟩ := u
  obtain ⟨ιv, fv, gv⟩ := v;
  simp +decide only [BEq_def, BMem_def];
  refine' le_trans ( inf_le_inf_right _ inf_le_left ) _;
  rw [ inf_iSup_eq, iSup_le_iff ];
  intro i
  have h_le : (⨅ i, gu i ⇨ ⨆ j, gv j ⊓ (⟦fu i =ᴮ fv j⟧)) ⊓ (gu i ⊓ (⟦x =ᴮ fu i⟧)) ≤ ⨆ j, gv j ⊓ (⟦fu i =ᴮ fv j⟧) ⊓ (⟦x =ᴮ fu i⟧) := by
    have h_le : (⨅ i, gu i ⇨ ⨆ j, gv j ⊓ (⟦fu i =ᴮ fv j⟧)) ⊓ (gu i ⊓ (⟦x =ᴮ fu i⟧)) ≤ (gu i ⇨ ⨆ j, gv j ⊓ (⟦fu i =ᴮ fv j⟧)) ⊓ (gu i ⊓ (⟦x =ᴮ fu i⟧)) := by
      exact inf_le_inf ( iInf_le _ _ ) le_rfl;
    refine' le_trans h_le _;
    simp +decide [ ← inf_assoc, ← iSup_inf_eq ];
    exact le_trans ( inf_le_left ) ( inf_le_left );
  refine' le_trans h_le ( iSup_mono fun j => _ );
  refine' le_trans _ ( inf_le_inf_left _ ( BEq_trans_le x ( fu i ) ( fv j ) ) );
  grind

/-
**Leibniz congruence (left argument of `∈`).**
`⟦u =ᴮ v⟧ ⊓ ⟦u ∈ᴮ x⟧ ≤ ⟦v ∈ᴮ x⟧`.
-/
theorem BEq_mem_congr_left (u v x : BSet B) : BEq u v ⊓ BMem u x ≤ BMem v x := by
  obtain ⟨ιx, fx, gx⟩ := x
  simp [BMem_def] at *;
  rw [ inf_iSup_eq ];
  refine' iSup_mono fun i => _;
  convert inf_le_inf_left ( gx i ) ( BEq_trans_le v u ( fx i ) ) using 1;
  rw [ BSet.BEq_symm ] ; ac_rfl

/-! ## Boolean-valued pairing -/

/-- The Boolean-valued unordered pair `{x, y}ᴮ`: two children `x`, `y`, each carrying
truth value `⊤`. -/
def bpair (x y : BSet B) : BSet B :=
  ⟨ULift.{u} Bool, fun b => bif b.down then x else y, fun _ => ⊤⟩

/-
The membership value of `{x, y}ᴮ` is the pairing disjunction.
-/
theorem BMem_bpair (z x y : BSet B) : BMem z (bpair x y) = BEq z x ⊔ BEq z y := by
  refine' le_antisymm _ _;
  · simp +decide [ BSet.BMem_def, BSet.bpair ];
  · refine' sup_le _ _;
    · refine' le_trans _ ( le_iSup _ ⟨ Bool.true ⟩ );
      aesop;
    · refine' le_iSup_of_le ⟨ Bool.false ⟩ _ ; simp

/-- **The pairing axiom holds in `V^B`.**  For any two names there is a name whose
membership value is exactly the pairing disjunction. -/
theorem forcing_pairing (x y : BSet B) :
    ∃ p : BSet B, ∀ z, BMem z p = BEq z x ⊔ BEq z y :=
  ⟨bpair x y, fun z => BMem_bpair z x y⟩

end BSet

/-- **Independence realised in `V^B`.**  Over the non-degenerate complete Boolean
algebra `Set (Fin 2)` there is a membership statement `φ` for which both `⟦φ⟧` and
`⟦¬φ⟧ = ⟦φ⟧ᶜ` are nonzero: neither `φ` nor its negation is forced by `⊤`.  This is
the algebraic core of every forcing independence result. -/
theorem BSet.bmem_undecided :
    ∃ (x y : BSet (Set (Fin 2))), ⊥ < BSet.BMem x y ∧ ⊥ < (BSet.BMem x y)ᶜ := by
  refine ⟨BSet.bempty, BSet.bsingleton {0}, ?_, ?_⟩
  · rw [BSet.BMem_bsingleton, bot_lt_iff_ne_bot]
    intro h; simpa using (Set.ext_iff.1 h 0)
  · rw [BSet.BMem_bsingleton, bot_lt_iff_ne_bot]
    intro h
    have h1 : (1 : Fin 2) ∈ ({0} : Set (Fin 2))ᶜ := by simp
    rw [h] at h1
    simp at h1

end RGF2
end RGF