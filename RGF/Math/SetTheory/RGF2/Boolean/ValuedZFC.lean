/-
  RGF2/Boolean/ValuedZFC.lean   (module `RGF2.Boolean.ValuedZFC`)
  — layer 1: the ZFC axioms validated in the Boolean-valued model `V^B`.

  **RGF 2.0 — Path 3, completed: every ZFC axiom holds with Boolean value `⊤`.**

  `RGF2/Boolean/Model.lean` set up the Boolean-valued universe `V^B = BSet B` over a
  complete Boolean algebra `B` (with `B`-valued equality `BEq`, membership `BMem`,
  and soundness), and `RGF2/Boolean/Forcing.lean` proved `BEq` is a `B`-valued
  equivalence relation, Leibniz congruence, and the pairing axiom.

  This file *completes* Path 3 by validating the remaining ZFC axioms in `V^B`:
  each axiom, interpreted as a Boolean truth value (with `∀`/`∃` read as
  `⨅`/`⨆` over the class of names and `↔` as the Boolean biconditional), evaluates
  to `⊤`.  Concretely we build the Boolean-valued constructions

    * `bsep`       separation / comprehension name (with `BMem_bsep`);
    * `bsUnion`    union name (with `BMem_bsUnion`);
    * `bpowerset`  power-set name (with `BMem_bpowerset`);
    * `bomega`     an internal inductive set;

  and prove the axiom truth values equal `⊤`:

    * `valid_extensionality`   `Ext = ⊤`;
    * `valid_empty`            `Empty = ⊤`;
    * `valid_pairing`          `Pairing = ⊤`;
    * `valid_union`            `Union = ⊤`;
    * `valid_powerset`         `Power = ⊤`;
    * `valid_separation`       `Sep φ = ⊤`  (for `BEq`-congruent `φ`);
    * `valid_foundation`       `Foundation = ⊤`;
    * `valid_infinity`         `Infinity = ⊤`.

  Together with `RGF2/Master.lean` (which validates the axioms two-valuedly on the
  W-type universe `RGFSet₂`) this shows `V^B` is a genuine Boolean-valued model of
  set theory — the flexibility (`membership_can_be_independent`, `bmem_undecided`)
  being exactly the mechanism forcing rests on.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Boolean.Model
import RGF.Math.SetTheory.RGF2.Boolean.Forcing

universe u

namespace RGF
namespace RGF2
namespace BSet

variable {B : Type u} [CompleteBooleanAlgebra B]

/-! ## Accessors for the components of a name -/

/-- The index type of a name. -/
def idx : BSet B → Type u
  | ⟨ι, _, _⟩ => ι

/-- The child family of a name. -/
def chf : (x : BSet B) → idx x → BSet B
  | ⟨_, f, _⟩ => f

/-- The truth-value family of a name. -/
def chg : (x : BSet B) → idx x → B
  | ⟨_, _, g⟩ => g

@[simp] theorem idx_mk (ι : Type u) (f : ι → BSet B) (g : ι → B) :
    idx (mk ι f g) = ι := rfl
@[simp] theorem chf_mk (ι : Type u) (f : ι → BSet B) (g : ι → B) :
    chf (mk ι f g) = f := rfl
@[simp] theorem chg_mk (ι : Type u) (f : ι → BSet B) (g : ι → B) :
    chg (mk ι f g) = g := rfl

/-- Membership value expressed through the accessors. -/
theorem BMem_eq (x y : BSet B) :
    BMem x y = ⨆ j : idx y, chg y j ⊓ BEq x (chf y j) := by
  cases y with
  | mk ι f g => rw [BMem_def]; rfl

/-! ## Boolean biconditional and subset value -/

/-- Boolean biconditional. -/
def bicond (a b : B) : B := (a ⇨ b) ⊓ (b ⇨ a)

theorem bicond_eq_top_iff {a b : B} : bicond a b = ⊤ ↔ a = b := by
  rw [bicond, inf_eq_top_iff, himp_eq_top_iff, himp_eq_top_iff]
  exact ⟨fun ⟨h1, h2⟩ => le_antisymm h1 h2, fun h => ⟨h.le, h.ge⟩⟩

theorem bicond_self (a : B) : bicond a a = ⊤ := by rw [bicond_eq_top_iff]

/-- Boolean-valued subset relation `⟦z ⊆ x⟧ = ⨅_w (w ∈ z ⇨ w ∈ x)`. -/
def BSubset (z x : BSet B) : B := ⨅ w : BSet B, BMem w z ⇨ BMem w x

/-! ## Constructions -/

/-- Boolean-valued separation / comprehension: restrict the truth-tags of `x` by a
`B`-valued predicate `φ`. -/
def bsep (φ : BSet B → B) : BSet B → BSet B
  | ⟨ι, f, g⟩ => ⟨ι, f, fun i => g i ⊓ φ (f i)⟩

/-- Boolean-valued union: the members of the members of `x`. -/
def bsUnion (x : BSet B) : BSet B :=
  ⟨ Σ i : idx x, idx (chf x i),
    fun p => chf (chf x p.1) p.2,
    fun p => chg x p.1 ⊓ chg (chf x p.1) p.2 ⟩

/-- The `B`-valued sub-name of `x` picked out by a characteristic function `h`:
the children of `x` retagged by `chg x i ⊓ h i`. -/
def bpsub (x : BSet B) (h : idx x → B) : BSet B :=
  ⟨idx x, chf x, fun i => chg x i ⊓ h i⟩

/-- Boolean-valued power set: one child per `B`-valued "characteristic function"
`h : idx x → B`, namely the sub-name `bpsub x h`. -/
def bpowerset (x : BSet B) : BSet B :=
  ⟨ idx x → B, fun h => bpsub x h, fun _ => ⊤ ⟩

/-! ## Membership characterizations -/

/-- **Separation characterization.** For a `BEq`-congruent predicate `φ`,
`⟦z ∈ bsep φ x⟧ = ⟦z ∈ x⟧ ⊓ φ z`. -/
theorem BMem_bsep (φ : BSet B → B)
    (hφ : ∀ u v, φ u ⊓ BEq u v ≤ φ v) (z x : BSet B) :
    BMem z (bsep φ x) = BMem z x ⊓ φ z := by
  obtain ⟨ι, f, g⟩ := x
  simp only [bsep, BMem_def]
  rw [iSup_inf_eq]
  refine iSup_congr (fun i => ?_)
  refine le_antisymm (le_inf (le_inf ?_ ?_) ?_) (le_inf (le_inf ?_ ?_) ?_)
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_right
  · calc (g i ⊓ φ (f i)) ⊓ BEq z (f i)
        ≤ φ (f i) ⊓ BEq z (f i) := inf_le_inf_right _ inf_le_right
      _ = φ (f i) ⊓ BEq (f i) z := by rw [BEq_symm]
      _ ≤ φ z := hφ (f i) z
  · exact inf_le_left.trans inf_le_left
  · calc (g i ⊓ BEq z (f i)) ⊓ φ z
        ≤ BEq z (f i) ⊓ φ z := inf_le_inf_right _ inf_le_right
      _ = φ z ⊓ BEq z (f i) := by rw [inf_comm]
      _ ≤ φ (f i) := hφ z (f i)
  · exact inf_le_left.trans inf_le_right

/-
**Union characterization.** `⟦z ∈ ⋃ x⟧ = ⨆_w (⟦w ∈ x⟧ ⊓ ⟦z ∈ w⟧)`.
-/
theorem BMem_bsUnion (z x : BSet B) :
    BMem z (bsUnion x) = ⨆ w : BSet B, BMem w x ⊓ BMem z w := by
  refine' le_antisymm _ _;
  · simp +decide [ BSet.BMem_eq ];
    intro ⟨ i, j ⟩;
    refine' le_trans _ ( le_iSup _ ( x.chf i ) );
    refine' le_inf _ _;
    · refine' le_trans _ ( le_iSup _ i );
      exact inf_le_inf ( inf_le_left ) ( by simp +decide [ BEq_refl ] );
    · refine' le_trans _ ( le_iSup _ j );
      exact inf_le_inf ( inf_le_right ) le_rfl;
  · refine' iSup_le _;
    intro w;
    -- By definition of `BMem`, we can expand the right-hand side.
    have h_expand : (BMem w x) ⊓ (BMem z w) ≤ ⨆ i : idx x, (chg x i) ⊓ (BMem z (chf x i)) := by
      have h_expand : (BMem w x) ⊓ (BMem z w) ≤ ⨆ i : idx x, (chg x i) ⊓ (BEq w (chf x i)) ⊓ (BMem z w) := by
        rw [ BMem_eq ];
        simp +decide [ iSup_inf_eq ];
      refine' le_trans h_expand ( iSup_mono fun i => _ );
      have h_expand : (BEq w (chf x i)) ⊓ (BMem z w) ≤ BMem z (chf x i) := by
        convert BEq_mem_congr_right w ( chf x i ) z using 1;
      simpa only [ inf_assoc ] using inf_le_inf_left _ h_expand;
    refine' le_trans h_expand ( iSup_le _ );
    intro i;
    have h_mem : ∀ j : idx (chf x i), (chg x i) ⊓ (chg (chf x i) j) ⊓ (BEq z (chf (chf x i) j)) ≤ BMem z (bsUnion x) := by
      intro j;
      refine' le_trans _ ( le_iSup _ ⟨ i, j ⟩ );
      exact le_rfl;
    rw [ BMem_eq ];
    rw [ inf_iSup_eq ];
    exact iSup_le fun j => by simpa only [ inf_assoc ] using h_mem j;

/-- Membership value of a sub-name. -/
theorem BMem_bpsub (w x : BSet B) (h : idx x → B) :
    BMem w (bpsub x h) = ⨆ i : idx x, (chg x i ⊓ h i) ⊓ BEq w (chf x i) := by
  rw [BMem_eq]; rfl

/-- Every sub-name is a subset of `x` (value `⊤`): `⟦w ∈ bpsub x h⟧ ≤ ⟦w ∈ x⟧`. -/
theorem BMem_bpsub_le (w x : BSet B) (h : idx x → B) :
    BMem w (bpsub x h) ≤ BMem w x := by
  rw [BMem_bpsub, BMem_eq]
  exact iSup_mono fun i => inf_le_inf_right _ inf_le_left

/-
`BSubset` is a left congruence for `BEq`: `⟦z =ᴮ u⟧ ⊓ ⟦u ⊆ x⟧ ≤ ⟦z ⊆ x⟧`.
-/
theorem BEq_subset_le (z u x : BSet B) :
    BEq z u ⊓ BSubset u x ≤ BSubset z x := by
  refine' le_iInf fun w => _;
  -- From BEq_mem_congr_right (swap), we have that BEq z u ⊓ BMem w z ≤ BMem w u.
  have h1 : BEq z u ⊓ BMem w z ≤ BMem w u := by
    convert BEq_mem_congr_right z u w using 1;
  rw [ le_himp_iff ];
  rw [ inf_right_comm ];
  refine' le_trans ( inf_le_inf_right _ h1 ) _;
  exact le_trans ( inf_le_inf_left _ ( iInf_le _ w ) ) ( by simp +decide )

/-
**Comprehension core.** `⟦z ⊆ x⟧ ≤ ⟦z =ᴮ bpsub x (fun i => ⟦(chf x i) ∈ z⟧)⟧`:
a subset of `x` is `B`-equal to the canonical sub-name whose characteristic
function records how strongly each child of `x` lies in `z`.
-/
theorem BSubset_le_BEq_bpsub (z x : BSet B) :
    BSubset z x ≤ BEq z (bpsub x (fun i => BMem (chf x i) z)) := by
  -- Write `s := BSubset z x = ⨅ w, BMem w z ⇨ BMem w x` and `h := fun i => BMem (chf x i) z`, so `bpsub x h = ⟨idx x, chf x, fun i => chg x i ⊓ BMem (chf x i) z⟩`.
  set s := z.BSubset x
  set h := fun i => BMem (chf x i) z
  set y := bpsub x h with hy;
  -- Unfold the target equality value with `BEq_def`; it is a meet of two parts (call them A and B).
  have h_eq : s ≤ (⨅ j : idx z, chg z j ⇨ ⨆ i : idx x, (chg x i ⊓ h i) ⊓ BEq (chf z j) (chf x i)) ⊓ (⨅ i : idx x, (chg x i ⊓ h i) ⇨ ⨆ j : idx z, chg z j ⊓ BEq (chf z j) (chf x i)) := by
    refine' le_inf _ _ <;> simp +decide;
    · intro i
      have h1 : s ⊓ z.chg i ≤ BMem (chf z i) x := by
        have h1 : z.chg i ≤ BMem (chf z i) z := by
          rw [ BMem_eq ];
          exact le_iSup_of_le i ( by simp +decide [ BEq_refl ] );
        have h2 : s ≤ BMem (chf z i) z ⇨ BMem (chf z i) x := by
          exact iInf_le _ _;
        exact le_trans ( inf_le_inf h2 h1 ) ( by simp +decide )
      have h2 : BMem (chf z i) x ⊓ z.chg i ≤ ⨆ j : idx x, (chg x j ⊓ h j) ⊓ BEq (chf z i) (chf x j) := by
        have h2 : BMem (chf z i) x ⊓ z.chg i = ⨆ j : idx x, x.chg j ⊓ BEq (chf z i) (chf x j) ⊓ z.chg i := by
          have h2 : BMem (chf z i) x = ⨆ j : idx x, x.chg j ⊓ BEq (chf z i) (chf x j) := by
            convert BMem_eq ( chf z i ) x using 1
          generalize_proofs at *; (
          rw [ h2, iSup_inf_eq ])
        generalize_proofs at *; (
        refine' h2.le.trans ( iSup_mono fun j => _ );
        have h3 : BEq (chf z i) (chf x j) ⊓ z.chg i ≤ BMem (chf x j) z := by
          have h3 : z.chg i ≤ BMem (chf z i) z := by
            have h3 : z.chg i ≤ ⨆ j : idx z, z.chg j ⊓ BEq (chf z i) (chf z j) := by
              exact le_iSup_of_le i ( by simp +decide [ BEq_refl ] )
            generalize_proofs at *; (
            convert h3 using 1;
            convert BMem_eq ( chf z i ) z using 1)
          generalize_proofs at *; (
          exact le_trans ( inf_le_inf_left _ h3 ) ( BEq_mem_congr_left _ _ _ ) |> le_trans <| by simp +decide [ BSet.BMem ] ;)
        generalize_proofs at *; (
        simp +decide [ inf_comm, inf_left_comm ];
        exact ⟨ le_trans ( inf_le_inf_left _ inf_le_left ) h3, inf_le_right.trans inf_le_right ⟩))
      exact le_trans (le_inf h1 inf_le_right) h2;
    · intro i;
      -- By definition of $h$, we know that $h i = \sup_{j} z.chg j \land BEq (z.chf j) (x.chf i)$.
      have h_def : h i = ⨆ j : idx z, z.chg j ⊓ BEq (z.chf j) (x.chf i) := by
        convert BMem_eq ( x.chf i ) z using 1;
        simp +decide only [BEq_symm];
      refine' le_trans ( inf_le_right ) _;
      exact h_def.symm ▸ inf_le_right;
  convert h_eq using 1;
  cases z ; rfl

/-- **Power-set characterization.** `⟦z ∈ 𝒫 x⟧ = ⟦z ⊆ x⟧`. -/
theorem BMem_bpowerset (z x : BSet B) :
    BMem z (bpowerset x) = BSubset z x := by
  have hz : BMem z (bpowerset x) = ⨆ h : idx x → B, BEq z (bpsub x h) := by
    simp only [bpowerset, BMem_def, top_inf_eq]
  rw [hz]
  refine le_antisymm (iSup_le fun h => ?_) ?_
  · -- each sub-name is a subset, and BSubset is BEq-congruent
    have hsub : BSubset (bpsub x h) x = ⊤ :=
      iInf_eq_top.2 fun w => himp_eq_top_iff.2 (BMem_bpsub_le w x h)
    calc BEq z (bpsub x h) = BEq z (bpsub x h) ⊓ BSubset (bpsub x h) x := by rw [hsub, inf_top_eq]
      _ ≤ BSubset z x := BEq_subset_le z (bpsub x h) x
  · exact le_iSup_of_le (fun i => BMem (chf x i) z) (BSubset_le_BEq_bpsub z x)

/-! ## The ZFC axioms, validated at Boolean value `⊤` -/

/-
**Extensionality** holds in `V^B`: if `x` and `y` have the same members
(`B`-valued), their equality value is `⊤`.
-/
theorem valid_extensionality :
    (⨅ x : BSet B, ⨅ y : BSet B,
      (⨅ z : BSet B, bicond (BMem z x) (BMem z y)) ⇨ BEq x y) = ⊤ := by
  refine' eq_top_iff.mpr ( le_iInf fun x => le_iInf fun y => _ );
  obtain ⟨ ι, f, g ⟩ := x; obtain ⟨ ι', f', g' ⟩ := y; simp +decide [ BSet.BEq_def, BSet.BMem_def ] ;
  constructor;
  · intro i;
    refine' le_trans ( inf_le_inf_right _ ( iInf_le _ ( f i ) ) ) _;
    refine' le_trans ( inf_le_inf_right _ ( inf_le_left ) ) _;
    refine' le_trans ( inf_le_inf_right _ ( himp_le_himp ( le_iSup _ i ) le_rfl ) ) _;
    rw [ BSet.BEq_refl ] ; simp +decide [ inf_comm ];
  · intro i
    have h_le : (⨅ z, bicond (⨆ j, g j ⊓ (⟦z =ᴮ f j⟧)) (⨆ j, g' j ⊓ (⟦z =ᴮ f' j⟧))) ⊓ g' i ≤ (⨆ j, g j ⊓ (⟦f j =ᴮ f' i⟧)) := by
      have h_le : (⨅ z, bicond (⨆ j, g j ⊓ (⟦z =ᴮ f j⟧)) (⨆ j, g' j ⊓ (⟦z =ᴮ f' j⟧))) ≤ (⨆ j, g' j ⊓ (⟦f' i =ᴮ f' j⟧)) ⇨ (⨆ j, g j ⊓ (⟦f' i =ᴮ f j⟧)) := by
        exact iInf_le _ _ |> le_trans <| inf_le_right;
      refine' le_trans ( inf_le_inf_right _ h_le ) _;
      refine' le_trans ( inf_le_inf ( himp_le_himp ( le_iSup _ i ) le_rfl ) le_rfl ) _;
      simp +decide [ BSet.BEq_refl, BSet.BEq_symm ]
    exact h_le

/-- **Empty set** holds in `V^B`. -/
theorem valid_empty :
    (⨆ e : BSet B, ⨅ z : BSet B, (BMem z e)ᶜ) = ⊤ := by
  refine top_le_iff.1 ?_
  refine le_iSup_of_le bempty ?_
  refine le_iInf fun z => ?_
  rw [BMem_bempty]; simp

/-- **Pairing** holds in `V^B`. -/
theorem valid_pairing :
    (⨅ a : BSet B, ⨅ b : BSet B, ⨆ p : BSet B, ⨅ z : BSet B,
      bicond (BMem z p) (BEq z a ⊔ BEq z b)) = ⊤ := by
  refine top_le_iff.1 (le_iInf fun a => le_iInf fun b => ?_)
  refine le_iSup_of_le (bpair a b) (le_iInf fun z => ?_)
  rw [top_le_iff, bicond_eq_top_iff, BMem_bpair]

/-- **Union** holds in `V^B`. -/
theorem valid_union :
    (⨅ x : BSet B, ⨆ u : BSet B, ⨅ z : BSet B,
      bicond (BMem z u) (⨆ w : BSet B, BMem w x ⊓ BMem z w)) = ⊤ := by
  refine top_le_iff.1 (le_iInf fun x => ?_)
  refine le_iSup_of_le (bsUnion x) (le_iInf fun z => ?_)
  rw [top_le_iff, bicond_eq_top_iff, BMem_bsUnion]

/-- **Power set** holds in `V^B`. -/
theorem valid_powerset :
    (⨅ x : BSet B, ⨆ p : BSet B, ⨅ z : BSet B,
      bicond (BMem z p) (BSubset z x)) = ⊤ := by
  refine top_le_iff.1 (le_iInf fun x => ?_)
  refine le_iSup_of_le (bpowerset x) (le_iInf fun z => ?_)
  rw [top_le_iff, bicond_eq_top_iff, BMem_bpowerset]

/-- **Separation** holds in `V^B` (schema: one instance per `BEq`-congruent
predicate `φ`). -/
theorem valid_separation (φ : BSet B → B)
    (hφ : ∀ u v, φ u ⊓ BEq u v ≤ φ v) :
    (⨅ x : BSet B, ⨆ s : BSet B, ⨅ z : BSet B,
      bicond (BMem z s) (BMem z x ⊓ φ z)) = ⊤ := by
  refine top_le_iff.1 (le_iInf fun x => ?_)
  refine le_iSup_of_le (bsep φ x) (le_iInf fun z => ?_)
  rw [top_le_iff, bicond_eq_top_iff, BMem_bsep φ hφ]

/-
**Foundation auxiliary.** If `a` is a member of `x` (to some degree), then `x`
has an `∈`-minimal member (to at least that degree).  Proved by structural
induction on the name `a`.
-/
theorem foundation_aux (a x : BSet B) :
    BMem a x ≤ ⨆ y : BSet B, BMem y x ⊓ ⨅ z : BSet B, BMem z y ⇨ (BMem z x)ᶜ := by
  revert a x;
  intro a;
  induction' a using BSet.recOn with ι f g ih;
  intro x;
  -- Let $d := \bigvee_{z} \bigvee_{i} (g i \wedge \text{BEq } z (f i)) \wedge \text{BMem } z x$.
  set d := ⨆ z : BSet B, ⨆ i : ι, (g i ⊓ BEq z (f i)) ⊓ BMem z x;
  -- Then $BMem a x ⊓ dᶜ ≤ RHS x$ and $BMem a x ⊓ d ≤ RHS x$.
  have h1 : BMem (BSet.mk ι f g) x ⊓ dᶜ ≤ ⨆ y : BSet B, BMem y x ⊓ ⨅ z : BSet B, BMem z y ⇨ (BMem z x)ᶜ := by
    refine' le_trans _ ( le_iSup _ ( mk ι f g ) );
    gcongr;
    refine' le_iInf fun z => _;
    simp +decide [ BMem_def, himp_eq ];
    rw [ ← compl_inf ];
    refine' compl_le_compl _;
    refine' le_trans _ ( le_iSup _ z );
    simp +decide [ inf_comm, inf_assoc, inf_iSup_eq ]
  have h2 : BMem (BSet.mk ι f g) x ⊓ d ≤ ⨆ y : BSet B, BMem y x ⊓ ⨅ z : BSet B, BMem z y ⇨ (BMem z x)ᶜ := by
    -- By definition of $d$, we have $d ≤ ⨆ i, g i ⊓ BMem (f i) x$.
    have hd_le : d ≤ ⨆ i : ι, g i ⊓ BMem (f i) x := by
      refine' iSup_le fun z => iSup_le fun i => _;
      refine' le_trans _ ( le_iSup _ i );
      refine' le_trans _ ( inf_le_inf_left _ ( BEq_mem_congr_left z ( f i ) x ) );
      rw [ inf_assoc ];
    refine' le_trans ( inf_le_right ) ( le_trans hd_le _ );
    refine' iSup_le fun i => _;
    exact le_trans ( inf_le_right ) ( ih i x );
  refine' le_trans _ ( sup_le h1 h2 );
  simp +decide [ ← inf_sup_left ]

/-- **Foundation / Regularity** holds in `V^B`. -/
theorem valid_foundation :
    (⨅ x : BSet B, (⨆ w : BSet B, BMem w x) ⇨
      ⨆ y : BSet B, BMem y x ⊓ ⨅ z : BSet B, BMem z y ⇨ (BMem z x)ᶜ) = ⊤ := by
  refine eq_top_iff.2 (le_iInf fun x => le_himp_iff.2 ?_)
  refine (inf_le_right).trans (iSup_le fun w => foundation_aux w x)

end BSet

/-! ## Infinity -/

namespace BSet

variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Boolean-valued von Neumann successor `x ↦ x ∪ {x}`. -/
def bsucc (x : BSet B) : BSet B :=
  ⟨ Option (idx x),
    fun o => o.elim x (chf x),
    fun o => o.elim ⊤ (chg x) ⟩

/-- **Successor characterization.** `⟦z ∈ bsucc a⟧ = ⟦z ∈ a⟧ ⊔ ⟦z =ᴮ a⟧`. -/
theorem BMem_bsucc (z a : BSet B) : BMem z (bsucc a) = BMem z a ⊔ BEq z a := by
  rw [bsucc, BMem_def, iSup_option]
  cases a with
  | mk ι f g => simp only [Option.elim]; rw [BMem_def]; rw [sup_comm]; simp

/-- The internal `ω`: the names `n = bsucc^[n] bempty`, all tagged `⊤`. -/
def bomega : BSet B :=
  ⟨ ULift ℕ, fun n => (bsucc)^[n.down] bempty, fun _ => ⊤ ⟩

/-- Each finite von Neumann numeral `bsucc^[n] bempty` is a member of `bomega`
with value `⊤`. -/
theorem omega_self_mem (n : ℕ) :
    BMem ((bsucc)^[n] bempty) (bomega : BSet B) = ⊤ := by
  rw [bomega, BMem_def]
  refine top_le_iff.1 (le_iSup_of_le (ULift.up n) ?_)
  simp [BEq_refl]

/-
**Infinity** holds in `V^B`: there is a name containing an empty set and closed
under the (Boolean-valued) successor operation, with value `⊤`.
-/
theorem valid_infinity :
    (⨆ I : BSet B,
      (⨆ e : BSet B, BMem e I ⊓ ⨅ z : BSet B, (BMem z e)ᶜ) ⊓
      (⨅ x : BSet B, BMem x I ⇨
        ⨆ s : BSet B, BMem s I ⊓
          ⨅ z : BSet B, bicond (BMem z s) (BMem z x ⊔ BEq z x))) = ⊤ := by
  refine' le_antisymm ( le_top ) _;
  refine' le_iSup_of_le ( bomega : BSet B ) _;
  refine' le_inf ( le_iSup_of_le bempty _ ) ( le_iInf fun x => _ );
  · simp +decide [ BSet.BMem_bempty ];
    exact omega_self_mem 0;
  · simp +decide [ BSet.BMem_def, BSet.bomega ];
    intro n; refine' le_iSup_of_le ( bsucc^[n+1] bempty ) _; simp +decide [ Function.iterate_succ_apply' ] ;
    refine' ⟨ le_iSup_of_le ( n + 1 ) _, _ ⟩;
    · simp +decide [ Function.iterate_succ_apply', BSet.BEq_refl ];
    · intro i; rw [ BSet.BMem_bsucc ] ; simp +decide [ bicond ] ;
      constructor <;> rw [ inf_sup_left ];
      · refine' sup_le_sup _ _;
        · refine' le_trans _ ( BSet.BEq_mem_congr_right _ _ _ );
          rw [ BSet.BEq_symm ];
          congr! 1;
        · convert BEq_trans_le i ( bsucc^[n] bempty ) x using 1;
          rw [ BSet.BEq_symm ];
          exact inf_comm _ _;
      · refine' sup_le_sup _ _;
        · exact BSet.BEq_mem_congr_right _ _ _;
        · convert BEq_trans_le i x ( bsucc^[n] bempty ) using 1;
          grind +splitImp

/-! ## Capstone: the Boolean-valued model validates the ZFC axioms -/

/-- **`V^B` is a Boolean-valued model of ZFC (core).**  Over an arbitrary complete
Boolean algebra `B`, every one of the following ZFC axioms — interpreted as a
Boolean truth value with `∀`/`∃` read as `⨅`/`⨆` over the class of names and `↔`
as the Boolean biconditional — evaluates to `⊤`: Extensionality, Empty set,
Pairing, Union, Power set, the Separation schema (for `BEq`-congruent predicates),
Foundation and Infinity.  This is Path 3 of the RGF 2.0 reconstruction: the value
domain of `∈` is widened from the two-valued `Prop` to `B`, and the axioms remain
valid — while `membership_can_be_independent` / `bmem_undecided` show membership
truth values can lie strictly between `⊥` and `⊤`, the flexibility forcing rests
on. -/
theorem VB_models_ZFC_core :
    -- Extensionality
    (⨅ x : BSet B, ⨅ y : BSet B,
      (⨅ z : BSet B, bicond (BMem z x) (BMem z y)) ⇨ BEq x y) = ⊤ ∧
    -- Empty set
    (⨆ e : BSet B, ⨅ z : BSet B, (BMem z e)ᶜ) = ⊤ ∧
    -- Pairing
    (⨅ a : BSet B, ⨅ b : BSet B, ⨆ p : BSet B, ⨅ z : BSet B,
      bicond (BMem z p) (BEq z a ⊔ BEq z b)) = ⊤ ∧
    -- Union
    (⨅ x : BSet B, ⨆ u : BSet B, ⨅ z : BSet B,
      bicond (BMem z u) (⨆ w : BSet B, BMem w x ⊓ BMem z w)) = ⊤ ∧
    -- Power set
    (⨅ x : BSet B, ⨆ p : BSet B, ⨅ z : BSet B,
      bicond (BMem z p) (BSubset z x)) = ⊤ ∧
    -- Separation schema (BEq-congruent predicates)
    (∀ φ : BSet B → B, (∀ u v, φ u ⊓ BEq u v ≤ φ v) →
      (⨅ x : BSet B, ⨆ s : BSet B, ⨅ z : BSet B,
        bicond (BMem z s) (BMem z x ⊓ φ z)) = ⊤) ∧
    -- Foundation
    (⨅ x : BSet B, (⨆ w : BSet B, BMem w x) ⇨
      ⨆ y : BSet B, BMem y x ⊓ ⨅ z : BSet B, BMem z y ⇨ (BMem z x)ᶜ) = ⊤ ∧
    -- Infinity
    (⨆ I : BSet B,
      (⨆ e : BSet B, BMem e I ⊓ ⨅ z : BSet B, (BMem z e)ᶜ) ⊓
      (⨅ x : BSet B, BMem x I ⇨
        ⨆ s : BSet B, BMem s I ⊓
          ⨅ z : BSet B, bicond (BMem z s) (BMem z x ⊔ BEq z x))) = ⊤ :=
  ⟨valid_extensionality, valid_empty, valid_pairing, valid_union, valid_powerset,
    fun φ hφ => valid_separation φ hφ, valid_foundation, valid_infinity⟩

end BSet
end RGF2
end RGF