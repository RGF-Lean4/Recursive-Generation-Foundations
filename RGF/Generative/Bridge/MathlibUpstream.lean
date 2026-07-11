/-
  RGF/MathlibUpstream.lean

  Direction IV(a) — Seamless integration with the mainstream Mathlib ecosystem.

  Complementing `MathlibBridge.lean` (which identifies the RGF number systems with
  Mathlib's `ℕ/ℤ/ℚ`), this file packages two kinds of results in an upstream-ready,
  fully general form:

  * **A reusable, general lemma.**  `isSimpleGroup_of_mulEquiv` transports the
    `IsSimpleGroup` property across a group isomorphism — a genuinely generic tool
    (no RGF-specific content) suitable for contribution to Mathlib.

  * **Identification of the RGF `A₅`.**  Using that transport, the framework's
    alternating group on five letters is identified with the standard Mathlib
    object: it is simple (`A5_isSimple`) of order `60` (`A5_card`), and any group
    isomorphic to it is simple as well (`isSimpleGroup_of_A5`).
-/
import Mathlib

open Equiv

namespace RGF.Upstream

/-! ## 1. A general, upstream-ready transport lemma -/

/-
**Transport of simplicity across an isomorphism.**  If `G ≃* H` and `G` is a
    simple group, then so is `H`.  This is fully general and Mathlib-worthy.
-/
theorem isSimpleGroup_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) [IsSimpleGroup G] : IsSimpleGroup H := by
  refine' { .. };
  · obtain ⟨ x, y, hxy ⟩ := ‹IsSimpleGroup G›.exists_pair_ne;
    exact ⟨ e x, e y, by simpa using hxy ⟩;
  · intro N hN;
    have := ‹IsSimpleGroup G›.2 ( N.comap e );
    simp_all +decide [ Subgroup.eq_bot_iff_forall, Subgroup.eq_top_iff' ];
    exact this ( by infer_instance ) |> Or.imp ( fun h x hx => by simpa using h ( e.symm x ) ( by simpa using hx ) ) fun h x => by simpa using h ( e.symm x ) ;

/-! ## 2. Identification of the RGF five-fold alternating group -/

/-- The RGF alternating group on five letters is Mathlib's `alternatingGroup (Fin 5)`,
    which is simple. -/
theorem A5_isSimple : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance

/-
Its order is `60 = 5!/2`.
-/
theorem A5_card : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_card_alternatingGroup (α := Fin 5)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  have h5 : Nat.factorial 5 = 120 := by decide
  rw [h5] at h
  omega

/-- Consequently any group isomorphic to `A₅` is simple. -/
theorem isSimpleGroup_of_A5 {H : Type*} [Group H]
    (e : alternatingGroup (Fin 5) ≃* H) : IsSimpleGroup H :=
  isSimpleGroup_of_mulEquiv e

end RGF.Upstream