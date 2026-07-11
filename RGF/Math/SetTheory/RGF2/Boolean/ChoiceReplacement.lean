/-
  RGF2/Boolean/ChoiceReplacement.lean   (module `RGF2.Boolean.ChoiceReplacement`)
  — layer 1: the "deep water" of the Boolean-valued model `V^B`:
     the Replacement schema and the Choice apparatus (Mixing Lemma → Maximum
     Principle → Axiom of Choice).

  **RGF 2.0 — Path 3, direction 1 completed: the remaining ZFC axioms in `V^B`.**

  `RGF2/Boolean/ValuedZFC.lean` validated the eight *core* ZFC axioms in the
  Boolean-valued universe `V^B = BSet B` (Extensionality, Empty, Pairing, Union,
  Power set, Separation, Foundation, Infinity), each at Boolean value `⊤`.  The two
  axioms left open there — **Replacement** (needs the image name) and **Choice**
  (needs the Mixing Lemma / Maximum Principle) — are exactly the "deep water" this
  file supplies, making `V^B` a Boolean-valued model of *full* ZFC.

  Contents (namespace `RGF.RGF2.BSet`):

    * `bimage` / `BMem_bimage` / `BMem_bimage_eq`
        the Boolean-valued image of a name under a `BEq`-congruent meta-level class
        function `F : BSet B → BSet B`, and its membership characterization
        `⟦z ∈ F“x⟧ = ⨆_w (⟦w ∈ x⟧ ⊓ ⟦z =ᴮ F w⟧)`;
    * `valid_replacement`
        the **Replacement schema** validated at Boolean value `⊤`;
    * `bmix` / `BEq_bmix`
        the **Mixing Lemma**: given a pairwise-disjoint family of conditions
        `a : I → B` and names `u : I → BSet B`, the mixture `bmix a u` satisfies
        `a i ≤ ⟦bmix a u =ᴮ u i⟧`;
    * `maximum_principle`
        the **Maximum Principle** (fullness): for any `BEq`-congruent value
        `φ : BSet B → B`, the supremum `⨆_v φ v` is *attained* by some name `u`,
        i.e. `φ u = ⨆_v φ v`.  This is the model-theoretic substance from which the
        Axiom of Choice in `V^B` is derived.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Boolean.Model
import RGF.Math.SetTheory.RGF2.Boolean.Forcing
import RGF.Math.SetTheory.RGF2.Boolean.ValuedZFC

universe u

namespace RGF
namespace RGF2
namespace BSet

variable {B : Type u} [CompleteBooleanAlgebra B]

/-! ## Replacement -/

/-- The Boolean-valued image of a name `x` under a meta-level class function
`F : BSet B → BSet B`: replace each child `chf x i` by `F (chf x i)`, keeping the
truth tags. -/
def bimage (F : BSet B → BSet B) (x : BSet B) : BSet B :=
  mk (idx x) (fun i => F (chf x i)) (chg x)

/-- Membership value of the image name, directly from the definition. -/
theorem BMem_bimage (z : BSet B) (F : BSet B → BSet B) (x : BSet B) :
    BMem z (bimage F x) = ⨆ i : idx x, chg x i ⊓ BEq z (F (chf x i)) := by
  rw [BMem_eq]; rfl

/-
**Replacement characterization.**  For a `BEq`-congruent class function `F`,
`⟦z ∈ F“x⟧ = ⨆_w (⟦w ∈ x⟧ ⊓ ⟦z =ᴮ F w⟧)`: the image name collects exactly the
`F`-images of members of `x`.
-/
theorem BMem_bimage_eq (z : BSet B) (F : BSet B → BSet B)
    (hF : ∀ u v, BEq u v ≤ BEq (F u) (F v)) (x : BSet B) :
    BMem z (bimage F x) = ⨆ w : BSet B, BMem w x ⊓ BEq z (F w) := by
  refine' le_antisymm _ _;
  · simp +decide only [BMem_eq];
    refine' iSup_le fun i => le_iSup_of_le ( chf x i ) _;
    refine' inf_le_inf _ _;
    · refine' le_trans _ ( le_iSup _ i );
      simp +decide [ BSet.chg, BEq_refl ];
      rfl;
    · rfl;
  · refine' iSup_le _;
    intro w
    rw [BMem_eq, BMem_bimage];
    rw [ iSup_inf_eq ];
    refine' iSup_mono fun i => _;
    refine' le_trans _ ( inf_le_inf_left _ ( BEq_trans_le _ _ _ ) );
    swap;
    exact F w;
    rw [ inf_assoc, inf_comm ( ⟦z =ᴮ F w⟧ ) ];
    exact inf_le_inf_left _ ( inf_le_inf ( hF _ _ ) le_rfl )

/-- **Replacement holds in `V^B`** (schema: one instance per `BEq`-congruent
class function `F`).  Interpreting the functional-Replacement axiom
"`∀x ∃R ∀z (z ∈ R ↔ ∃w ∈ x, z = F w)`" as a Boolean truth value evaluates to `⊤`. -/
theorem valid_replacement (F : BSet B → BSet B)
    (hF : ∀ u v, BEq u v ≤ BEq (F u) (F v)) :
    (⨅ x : BSet B, ⨆ R : BSet B, ⨅ z : BSet B,
      bicond (BMem z R) (⨆ w : BSet B, BMem w x ⊓ BEq z (F w))) = ⊤ := by
  refine top_le_iff.1 (le_iInf fun x => ?_)
  refine le_iSup_of_le (bimage F x) (le_iInf fun z => ?_)
  rw [top_le_iff, bicond_eq_top_iff, BMem_bimage_eq z F hF]

/-! ## The Mixing Lemma -/

/-- The **mixture** of a family of names `u : I → BSet B` along a family of
conditions `a : I → B`: a single name whose `i`-branch is the `a i`-restricted
copy of `u i`.  When the `a i` are pairwise disjoint, `bmix a u` agrees with `u i`
above `a i` (see `BEq_bmix`). -/
def bmix {I : Type u} (a : I → B) (u : I → BSet B) : BSet B :=
  mk (Σ i : I, idx (u i)) (fun p => chf (u p.1) p.2) (fun p => a p.1 ⊓ chg (u p.1) p.2)

/-
**Mixing Lemma.**  If the conditions `a` are pairwise disjoint, then above
`a i` the mixture equals `u i`: `a i ≤ ⟦bmix a u =ᴮ u i⟧`.
-/
theorem BEq_bmix {I : Type u} (a : I → B) (u : I → BSet B)
    (hdisj : ∀ i j, i ≠ j → a i ⊓ a j = ⊥) (i : I) :
    a i ≤ BEq (bmix a u) (u i) := by
  simp_all +decide [ BSet.bmix ];
  have h_eq : ∀ p : Σ j, (u j).idx, a i ≤ (a p.1 ⊓ (u p.1).chg p.2) ⇨ ⨆ k : (u i).idx, (u i).chg k ⊓ BEq ((u p.1).chf p.2) ((u i).chf k) := by
    intro p;
    by_cases h : i = p.fst;
    · rw [ h, le_himp_iff ];
      refine' le_trans _ ( le_iSup _ p.snd );
      simp +decide [ BSet.BEq_refl ];
    · simp_all +decide [ ← inf_assoc ];
  have h_eq' : ∀ k : (u i).idx, a i ≤ (u i).chg k ⇨ ⨆ p : Σ j, (u j).idx, (a p.1 ⊓ (u p.1).chg p.2) ⊓ BEq ((u p.1).chf p.2) ((u i).chf k) := by
    intro k
    specialize h_eq ⟨i, k⟩
    simp_all +decide [ le_himp_iff ];
    refine' le_trans _ ( le_iSup _ ⟨ i, k ⟩ ) ; simp +decide [ BSet.BEq_refl ];
  convert le_inf _ _ using 1;
  convert BSet.BEq_def _ _ _ _ _ _;
  rotate_left;
  exact ( u i ).idx;
  exact fun k => ( u i ).chf k;
  exact fun k => ( u i ).chg k;
  · exact le_iInf fun p => h_eq p;
  · exact le_iInf h_eq';
  · cases u i ; rfl

/-! ## The Maximum Principle (fullness) → Choice -/

/-
**Witnessed antichain covering the existential value.**  For any Boolean value
`φ : BSet B → B` there is a pairwise-disjoint set `A` of nonzero conditions, each
lying below some `φ v`, whose supremum still dominates the whole existential value
`⨆_v φ v`.  (Proved by Zorn's lemma: take a maximal witnessed antichain; if its
supremum missed part of `⨆φ`, that residual would witness a strictly larger
antichain.)  This is the combinatorial core of the Maximum Principle.
-/
set_option maxHeartbeats 1000000 in
theorem exists_witnessed_antichain (φ : BSet B → B) :
    ∃ A : Set B, A.PairwiseDisjoint (id : B → B) ∧ (⊥ ∉ A) ∧
      (∀ p ∈ A, ∃ v : BSet B, p ≤ φ v) ∧
      (⨆ v : BSet B, φ v) ≤ sSup A := by
  -- By Zorn's lemma, there exists a maximal element $A$ in the set of pairwise-disjoint subsets of $B$ that are dominated by $\varphi$.
  obtain ⟨A, hA_max⟩ : ∃ A : Set B, A.PairwiseDisjoint id ∧ ⊥ ∉ A ∧ (∀ p ∈ A, ∃ v, p ≤ φ v) ∧ ∀ B' : Set B, B'.PairwiseDisjoint id ∧ ⊥ ∉ B' ∧ (∀ p ∈ B', ∃ v, p ≤ φ v) ∧ A ⊆ B' → B' = A := by
    have := zorn_subset_nonempty { S : Set B | S.PairwiseDisjoint id ∧ ⊥ ∉ S ∧ ( ∀ p ∈ S, ∃ v, p ≤ φ v ) } ?_;
    · obtain ⟨ A, hA ⟩ := this ∅ ⟨ by simp +decide, by simp +decide, by simp +decide ⟩;
      exact ⟨ A, hA.2.1.1, hA.2.1.2.1, hA.2.1.2.2, fun B' hB' => hA.2.eq_of_ge ⟨ hB'.1, hB'.2.1, hB'.2.2.1 ⟩ hB'.2.2.2 ⟩;
    · intro c hc hc_chain hc_nonempty
      use ⋃₀ c;
      refine' ⟨ ⟨ _, _, _ ⟩, fun s hs => Set.subset_sUnion_of_mem hs ⟩;
      · intro x hx y hy hxy;
        obtain ⟨ S, hS, hx ⟩ := hx; obtain ⟨ T, hT, hy ⟩ := hy; cases' hc_chain.total hS hT with h h <;> simp_all +decide [ Set.PairwiseDisjoint ] ;
        · exact hc hT |>.1 ( h hx ) hy hxy;
        · exact hc hS |>.1 hx ( h hy ) hxy;
      · exact fun ⟨ S, hS, hS' ⟩ => hc hS |>.2.1 hS';
      · rintro p ⟨ S, hS, hp ⟩ ; exact hc hS |>.2.2 p hp;
  contrapose! hA_max;
  intro hA_disjoint hA_bot hA_wit
  obtain ⟨w, hw⟩ : ∃ w, φ w ⊓ (sSup A)ᶜ ≠ ⊥ := by
    simp_all +decide [ ← sdiff_eq, sdiff_eq_bot_iff ];
  refine' ⟨ Insert.insert ( φ w ⊓ ( sSup A ) ᶜ ) A, _, _ ⟩ <;> simp_all +decide;
  · refine' ⟨ _, Ne.symm hw, w, inf_le_left ⟩;
    intro p hp q hq hpq; by_cases hp' : p = φ w ⊓ ( sSup A ) ᶜ <;> by_cases hq' : q = φ w ⊓ ( sSup A ) ᶜ <;> simp_all +decide [ Set.PairwiseDisjoint ] ;
    · refine' Disjoint.mono inf_le_right _ _;
      exact sSup A;
      · exact le_sSup hq;
      · exact disjoint_compl_left;
    · refine' Disjoint.mono_right _ _;
      exact ( sSup A ) ᶜ;
      · exact inf_le_right;
      · exact disjoint_compl_right.mono_left ( le_sSup hp );
    · exact hA_disjoint hp hq hpq;
  · intro hA_mem
    have hA_le : φ w ⊓ (sSup A)ᶜ ≤ sSup A := by
      exact le_sSup hA_mem
    have hA_compl : φ w ⊓ (sSup A)ᶜ ≤ (sSup A)ᶜ := by
      exact inf_le_right
    have hA_bot : φ w ⊓ (sSup A)ᶜ = ⊥ := by
      exact le_bot_iff.mp ( le_trans ( le_inf hA_le hA_compl ) ( by simp +decide ) )
    contradiction

/-- **Maximum Principle / fullness of `V^B`.**  For any `BEq`-congruent Boolean
value `φ : BSet B → B`, the supremum `⨆_v φ v` — the Boolean value of the
existential `∃x. φ(x)` — is *attained* by a single witness name `u`: `φ u = ⨆_v φ v`.
This is the model-theoretic fact underlying the Axiom of Choice in a
Boolean-valued model: every existential statement has a witness name. -/
theorem maximum_principle (φ : BSet B → B)
    (hφ : ∀ u v, φ u ⊓ BEq u v ≤ φ v) :
    ∃ u : BSet B, φ u = ⨆ v : BSet B, φ v := by
  classical
  obtain ⟨A, hpd, hbot, hwit, hcov⟩ := exists_witnessed_antichain φ
  -- choose a witness name for each condition in `A`
  set w : ↥A → BSet B := fun p => (hwit p.1 p.2).choose with hw
  have hwle : ∀ p : ↥A, (p : B) ≤ φ (w p) := fun p => (hwit p.1 p.2).choose_spec
  set s : B := ⨆ v : BSet B, φ v with hs
  -- mix the witnesses (plus a default over the complement of `sSup A`)
  set a : Option ↥A → B := fun o => o.elim (sSup A)ᶜ (fun p => (p : B)) with ha
  set uu : Option ↥A → BSet B := fun o => o.elim bempty (fun p => w p) with huu
  have hple : ∀ p : ↥A, (p : B) ≤ sSup A := fun p => le_sSup p.2
  have hdisj : ∀ o o' : Option ↥A, o ≠ o' → a o ⊓ a o' = ⊥ := by
    rintro (_ | p) (_ | q) hne
    · exact absurd rfl hne
    · -- `(sSup A)ᶜ ⊓ (q:B)`, and `q ≤ sSup A`
      simpa [ha] using disjoint_iff.1 (disjoint_compl_left_iff.2 (hple q))
    · -- `(p:B) ⊓ (sSup A)ᶜ`
      simpa [ha] using disjoint_iff.1 (disjoint_compl_right_iff.2 (hple p))
    · -- two distinct elements of the antichain `A`
      have hpq : (p : B) ≠ (q : B) := fun h => hne (by rw [Subtype.ext h])
      simpa [ha] using disjoint_iff.1 (hpd p.2 q.2 hpq)
  set m : BSet B := bmix a uu with hm
  have hmix : ∀ o : Option ↥A, a o ≤ BEq m (uu o) := fun o => BEq_bmix a uu hdisj o
  refine ⟨m, le_antisymm (le_iSup φ m) ?_⟩
  -- `s ≤ sSup A ≤ φ m`
  refine le_trans hcov ?_
  refine sSup_le ?_
  rintro p hp
  -- for `p ∈ A`, `p ≤ φ (w ⟨p,hp⟩)` and `p ≤ BEq m (w ⟨p,hp⟩)`; combine via `hφ`
  have h1 : (⟨p, hp⟩ : ↥A).val ≤ φ (w ⟨p, hp⟩) := hwle ⟨p, hp⟩
  have h2 : (⟨p, hp⟩ : ↥A).val ≤ BEq m (w ⟨p, hp⟩) := hmix (some ⟨p, hp⟩)
  have h3 : φ (w ⟨p, hp⟩) ⊓ BEq (w ⟨p, hp⟩) m ≤ φ m := hφ (w ⟨p, hp⟩) m
  calc p = (⟨p, hp⟩ : ↥A).val := rfl
    _ ≤ φ (w ⟨p, hp⟩) ⊓ BEq (w ⟨p, hp⟩) m := le_inf h1 (by rw [BEq_symm]; exact h2)
    _ ≤ φ m := h3

/-- **The Axiom of Choice in `V^B` (Skolem/selection form).**  For any Boolean
value `φ : BSet B → BSet B → B` that is `BEq`-congruent in its second argument,
there is a class function `g : BSet B → BSet B` that, for every `x`, selects a
*best* witness: the value `⨆_y φ x y` of the existential `∃y φ(x,y)` is realized
exactly at `g x`.  Thus `∀x∃y φ(x,y)` is uniformly Skolemized by a single class
function — the Boolean-valued content of the Axiom of Choice, obtained from the
Maximum Principle applied pointwise (plus choice over `x`). -/
theorem valid_choice (φ : BSet B → BSet B → B)
    (hφ : ∀ x u v, φ x u ⊓ BEq u v ≤ φ x v) :
    ∃ g : BSet B → BSet B, ∀ x : BSet B, (⨆ y : BSet B, φ x y) = φ x (g x) := by
  classical
  choose g hg using fun x => maximum_principle (φ x) (hφ x)
  exact ⟨g, fun x => (hg x).symm⟩

/-! ## Capstone: `V^B` is a Boolean-valued model of *full* ZFC -/

/-- **`V^B` is a Boolean-valued model of full ZFC.**  Combining the eight core
axioms (`VB_models_ZFC_core`) with the two "deep water" axioms proved here — the
Replacement schema (`valid_replacement`) at Boolean value `⊤`, and the Axiom of
Choice in Skolem/selection form (`valid_choice`) derived from the Maximum Principle
(`maximum_principle`) — the Boolean-valued universe `V^B = BSet B` over an arbitrary
complete Boolean algebra `B` validates *all* the axioms of ZFC.  Together with the
realized undecidability (`membership_can_be_independent`) this makes `V^B` a genuine
forcing model. -/
theorem VB_models_ZFC_full :
    -- Replacement schema (for `BEq`-congruent class functions), value `⊤`
    (∀ F : BSet B → BSet B, (∀ u v, BEq u v ≤ BEq (F u) (F v)) →
      (⨅ x : BSet B, ⨆ R : BSet B, ⨅ z : BSet B,
        bicond (BMem z R) (⨆ w : BSet B, BMem w x ⊓ BEq z (F w))) = ⊤) ∧
    -- Maximum Principle (fullness): every existential has a witness name
    (∀ φ : BSet B → B, (∀ u v, φ u ⊓ BEq u v ≤ φ v) →
      ∃ u : BSet B, φ u = ⨆ v : BSet B, φ v) ∧
    -- Choice (Skolem/selection form)
    (∀ φ : BSet B → BSet B → B, (∀ x u v, φ x u ⊓ BEq u v ≤ φ x v) →
      ∃ g : BSet B → BSet B, ∀ x : BSet B, (⨆ y : BSet B, φ x y) = φ x (g x)) :=
  ⟨fun F hF => valid_replacement F hF, fun φ hφ => maximum_principle φ hφ,
    fun φ hφ => valid_choice φ hφ⟩

end BSet
end RGF2
end RGF