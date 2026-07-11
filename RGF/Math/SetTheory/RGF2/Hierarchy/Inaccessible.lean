/-
  RGF2/Hierarchy/Inaccessible.lean   (module `RGF2.Hierarchy.Inaccessible`)
  — layer 1: large cardinals and the *conditional* consistency-strength ladder.

  **RGF 2.0 — Path 2/3, direction 3.1: a strong universe (inaccessible cardinal)
  yields a set-sized model of ZFC.**

  Gödel's second incompleteness theorem forbids proving `Con(ZFC)` *unconditionally*
  inside ZFC.  The honest, achievable statement is therefore **relative**: assuming a
  large cardinal, ZFC has a model.  This file proves exactly that, in its
  model-theoretic (semantic) form:

    * if there exists a strongly **inaccessible cardinal** `c`, then the von Neumann
      stage `V_ c.ord` is a transitive set that satisfies every ZFC axiom (as an
      internal closure/satisfaction property).

  This is the standard way the consistency-strength ladder

      PA  <  ZF−∞  <  ZFC  <  ZFC + "there is an inaccessible"  <  …

  is realized: an inaccessible cardinal is strictly stronger than ZFC precisely
  because it produces a *set* model of ZFC (whence, by the soundness theorem,
  `Con(ZFC)`).  The essential use of inaccessibility (regular + strong limit) is in
  the **Replacement** clause: the image of a set of size `< c` under a class function
  into `V_ c.ord` stays bounded below `c.ord` by regularity.

  Contents (namespace `RGF.RGF2`):

    * `IsZFCModel`                 the semantic ZFC-model predicate on a `ZFSet`
                                   (transitivity + closure under Pairing, Union,
                                   Power set, Separation, Replacement, and `ω`);
    * `preBeth_lt_of_lt_ord`       for inaccessible `c`, `preBeth o < c` when
                                   `o < c.ord` (the strong-limit + regular induction);
    * `card_lt_of_rank_lt`         a set of rank `< c.ord` has cardinality `< c`;
    * `rank_image_lt`              the Replacement rank bound (uses regularity);
    * `rank_omega_lt`              `rank ω < c.ord`;
    * `inaccessible_imp_ZFCmodel`  **the headline conditional theorem**:
                                   `(∃ c, c.IsInaccessible) → ∃ M, IsZFCModel M`.
-/
import Mathlib

open ZFSet Cardinal Ordinal

universe u

namespace RGF
namespace RGF2

/-- **Semantic ZFC-model predicate.**  A `ZFSet` `M` is a model of ZFC when it is
transitive and closed under the ZFC set-forming operations: Pairing, (arbitrary)
Union, Power set, the Separation schema, the Replacement schema, and contains the
inductive set `ω` (Infinity).  Extensionality and Foundation hold automatically for
a transitive `M ⊆ V`.  (Choice holds in `M` as well, inherited from the ambient
universe via Replacement; it is not needed for the consistency conclusion.) -/
def IsZFCModel (M : ZFSet.{u}) : Prop :=
  M.IsTransitive ∧
  (∀ x ∈ M, ∀ y ∈ M, ({x, y} : ZFSet) ∈ M) ∧
  (∀ x ∈ M, (⋃₀ x) ∈ M) ∧
  (∀ x ∈ M, (ZFSet.powerset x) ∈ M) ∧
  (∀ x ∈ M, ∀ p : ZFSet → Prop, (ZFSet.sep p x) ∈ M) ∧
  (∀ x ∈ M, ∀ F : ZFSet → ZFSet, (∀ y ∈ x, F y ∈ M) →
      ∃ R ∈ M, ∀ z, z ∈ R ↔ ∃ y ∈ x, F y = z) ∧
  (ZFSet.omega ∈ M)

variable {c : Cardinal.{u}}

/-- For a strongly inaccessible `c`, the pre-beth function stays below `c` on all
ordinals `< c.ord`.  Proved by transfinite induction: `preBeth 0 = 0 < c`, the
successor step uses the strong-limit property (`2 ^ κ' < c` for `κ' < c`), and the
limit step uses regularity (a supremum of `< c` many cardinals `< c` is `< c`). -/
theorem preBeth_lt_of_lt_ord (hc : c.IsInaccessible) {o : Ordinal} (ho : o < c.ord) :
    preBeth o < c := by
  induction o using Ordinal.induction with
  | _ o ih =>
    rcases Ordinal.zero_or_succ_or_isSuccLimit o with h0 | ⟨a, rfl⟩ | hlim
    · subst h0; rw [preBeth_zero]; exact hc.pos
    · rw [preBeth_succ]
      exact hc.isStrongLimit.two_power_lt (ih a (Order.lt_succ a) ((Order.lt_succ a).trans ho))
    · rw [preBeth_limit hlim.isSuccPrelimit]
      have hsurj : Function.Surjective
          (fun b : Shrink.{u} (Set.Iio o) => ((equivShrink (Set.Iio o)).symm b)) :=
        (equivShrink _).symm.surjective
      rw [← hsurj.iSup_comp (g := fun a : Set.Iio o => preBeth (a : Ordinal))]
      apply Cardinal.iSup_lt_of_isRegular hc.isRegular
      · have hsh : #(Shrink.{u} (Set.Iio o)) = o.card := by
          have h := Cardinal.lift_mk_shrink''.{u+1, u} (Set.Iio o)
          rw [Ordinal.mk_Iio_ordinal] at h
          exact Cardinal.lift_injective h
        rw [hsh]; exact Cardinal.lt_ord.1 ho
      · intro b
        exact ih _ ((equivShrink (Set.Iio o)).symm b).2
          (((equivShrink (Set.Iio o)).symm b).2.trans ho)

/-- A set of rank `< c.ord` has cardinality `< c` (uses the strong-limit bound
via `preBeth`). -/
theorem card_lt_of_rank_lt (hc : c.IsInaccessible) {x : ZFSet.{u}} (hx : x.rank < c.ord) :
    x.card < c := by
  have hsub : x ⊆ V_ x.rank := by
    intro y hy; rw [mem_vonNeumann]; exact rank_lt_of_mem hy
  calc x.card ≤ (V_ x.rank).card := ZFSet.card_mono hsub
    _ = preBeth x.rank := card_vonNeumann _
    _ < c := preBeth_lt_of_lt_ord hc hx

/-- **The Replacement rank bound (heart of the argument).**  If `x` has rank
`< c.ord` and a class function `f` sends each member of `x` into `V_ c.ord`, then the
image `image f x` also has rank `< c.ord`.  This is where regularity of `c` is
essential: the image is indexed by the `< c` elements of `x`, so its rank supremum
stays below `c.ord`. -/
theorem rank_image_lt (hc : c.IsInaccessible) {x : ZFSet.{u}}
    (f : ZFSet.{u} → ZFSet.{u}) [Definable₁ f]
    (hx : x.rank < c.ord) (hf : ∀ y ∈ x, (f y).rank < c.ord) :
    (image f x).rank < c.ord := by
  have hlim : Order.IsSuccLimit c.ord := isSuccLimit_ord hc.aleph0_lt.le
  set g : Shrink.{u} (↑↑x) → Ordinal.{u} :=
    fun b => Order.succ (f (((equivShrink (↑↑x)).symm b : ↑↑x) : ZFSet)).rank with hg
  have hidx : #(Shrink.{u} (↑↑x)) < c := by
    have h := Cardinal.lift_mk_shrink''.{u+1, u} (↑↑x)
    rw [ZFSet.cardinalMk_coe_sort] at h
    have hsh : #(Shrink.{u} (↑↑x)) = x.card := Cardinal.lift_injective h
    rw [hsh]; exact card_lt_of_rank_lt hc hx
  have hbound : iSup g < c.ord := by
    apply Cardinal.iSup_lt_ord_of_isRegular hc.isRegular hidx
    intro b
    exact hlim.succ_lt (hf _ (((equivShrink (↑↑x)).symm b : ↑↑x)).2)
  refine lt_of_le_of_lt ?_ hbound
  rw [rank_le_iff]
  intro z hz
  rw [mem_image] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hb := Ordinal.le_iSup g (equivShrink (↑↑x) ⟨y, hy⟩)
  simp only [hg, Equiv.symm_apply_apply] at hb
  exact lt_of_lt_of_le (Order.lt_succ _) hb

/-
`rank ω < c.ord` for an inaccessible `c` (since `ω = ℵ₀.ord < c.ord`).
-/
theorem rank_omega_lt (hc : c.IsInaccessible) :
    (ZFSet.omega.{u}).rank < c.ord := by
  refine' lt_of_le_of_lt _ ( Cardinal.ord_lt_ord.mpr hc.aleph0_lt );
  refine' Ordinal.iSup_le fun x => _;
  induction x ; simp +decide;
  induction ‹ℕ› <;> simp_all +decide [ PSet.ofNat ];
  rw [ Ordinal.lt_omega0 ] at *;
  rcases ‹_› with ⟨ n, hn ⟩ ; exact ⟨ n + 1, by simp +decide [ hn ] ⟩

/-- **Direction 3.1 — conditional consistency of ZFC.**  If there is a strongly
inaccessible cardinal, then there is a transitive set that is a model of ZFC (in the
semantic sense of `IsZFCModel`).  By the soundness theorem this witnesses `Con(ZFC)`:
the existence of an inaccessible cardinal is a strictly stronger theory than ZFC.

The model is the von Neumann stage `V_ c.ord`.  Its closure properties follow from
the rank calculus: `c.ord` is a limit ordinal (as `c` is an infinite cardinal), so
`V_ c.ord` is closed under Pairing, Union, Power set and Separation; it contains `ω`;
and it is closed under Replacement by `rank_image_lt` (the step that genuinely uses
inaccessibility). -/
theorem inaccessible_imp_ZFCmodel (h : ∃ c : Cardinal.{u}, c.IsInaccessible) :
    ∃ M : ZFSet.{u}, IsZFCModel M := by
  classical
  obtain ⟨c, hc⟩ := h
  have hlim : Order.IsSuccLimit c.ord := isSuccLimit_ord hc.aleph0_lt.le
  refine ⟨V_ c.ord, isTransitive_vonNeumann _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Pairing
    intro x hx y hy
    rw [mem_vonNeumann] at *
    rw [rank_pair]
    exact max_lt (hlim.succ_lt hx) (hlim.succ_lt hy)
  · -- Union
    intro x hx
    rw [mem_vonNeumann] at *
    exact (rank_sUnion_le x).trans_lt hx
  · -- Power set
    intro x hx
    rw [mem_vonNeumann] at *
    rw [rank_powerset]
    exact hlim.succ_lt hx
  · -- Separation
    intro x hx p
    rw [mem_vonNeumann] at *
    exact (rank_mono ZFSet.sep_subset).trans_lt hx
  · -- Replacement
    intro x hx F hF
    haveI : Definable₁ F := Classical.allZFSetDefinable (fun s => F (s 0))
    have hxr : x.rank < c.ord := by rwa [mem_vonNeumann] at hx
    have hFr : ∀ y ∈ x, (F y).rank < c.ord := by
      intro y hy; have := hF y hy; rwa [mem_vonNeumann] at this
    refine ⟨image F x, ?_, ?_⟩
    · rw [mem_vonNeumann]; exact rank_image_lt hc F hxr hFr
    · intro z; exact mem_image
  · -- Infinity
    rw [mem_vonNeumann]; exact rank_omega_lt hc

end RGF2
end RGF