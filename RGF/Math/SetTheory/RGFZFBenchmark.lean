/-
  Foundations/RGFZFBenchmark.lean

  **Phase 1 — Benchmark alignment with standard ZF set theory.**

  The companion files `Foundations/RGFSetTheory.lean` and
  `Foundations/RGFInfinity.lean` build a model of ZF − Infinity on the Ackermann
  codes `(ℕ, ∈ₐ)` and transport it onto the generative reals `RGFReal'` through
  the embedding `RVal`.  Those proofs are stated in *first-order* form (a predicate
  `Mem`/`RMem` on the carrier), which is mathematically correct but does not, by
  itself, line the construction up *literally* against a textbook ZF universe.

  This file supplies that benchmark.  Standard ZF has no notion of `RVal` or of an
  Ackermann encoding, so we give an **explicit translation function**

      `toZF : ℕ → ZFSet`            (Ackermann code ↦ genuine ZF set)
      `transZF : RGFReal' → ZFSet`  (RGF real ↦ genuine ZF set)

  into Mathlib's `ZFSet` (the standard von-Neumann ZF universe), and prove:

  * **Membership preservation** (`toZF_mem_toZF`, `transZF_preserves_mem`): the
    encoded membership relation corresponds *exactly* to real `∈` in `ZFSet`.  This
    is what lets us say "HF satisfies the first eight ZF axioms" without any appeal
    to "intuitive equivalence".

  * **The first eight ZF axioms, in literal `ZFSet` language**, hold for the
    hereditarily finite subuniverse `HF ⊆ ZFSet` (Extensionality, Empty set,
    Pairing, Union, Power set, Separation, Replacement, Foundation):
    `hf_*` closure lemmas + `zf_*` axiom statements.

  * **The Axiom of Infinity, with the textbook `IsInductiveSet` definition**, is
    *true* in the full `ZFSet` universe (`exists_isInductiveSet`, witnessed by
    `ZFSet.omega`) but **strictly fails** on `HF` (`no_inductiveSet_HF`).  The
    internal failure `no_inductive_set` is shown to be exactly the negation of the
    standard one (`isInductiveSet_toZF_iff`).

  * **`Univ` is the standard HF universe** (`range_toZF_eq_isHF`,
    `transZF_image_univ_eq_isHF`): the bidirectional characterization of the
    hereditarily finite sets.
-/
import Mathlib
import RGF.Math.Real.RGFInfinity

namespace RGF
namespace RGFSet

open RGFReal' ZFSet

/-! ## The translation `toZF : ℕ → ZFSet` -/

/-- Translate an Ackermann code `n` into the genuine ZF set it denotes:
    `toZF n = { toZF a | a ∈ₐ n }`. -/
noncomputable def toZF (n : ℕ) : ZFSet :=
  ZFSet.range (fun a : {a : ℕ // a ∈ elems n} => toZF a.1)
termination_by n
decreasing_by
  have := a.2; rw [mem_elems] at this; exact testBit_lt n a.1 this

/-- The defining membership property of the translation. -/
theorem mem_toZF (n : ℕ) (x : ZFSet) : x ∈ toZF n ↔ ∃ a, Mem a n ∧ toZF a = x := by
  rw [toZF, ZFSet.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, by have := i.2; rw [mem_elems] at this; exact this, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, by rw [mem_elems]; exact ha⟩, rfl⟩

/-- `toZF 0` is the empty ZF set. -/
theorem toZF_zero : toZF 0 = ∅ := by
  apply ZFSet.ext; intro z
  rw [mem_toZF]
  constructor
  · rintro ⟨a, ha, _⟩; exact absurd ha (empty a)
  · intro h; exact absurd h (ZFSet.notMem_empty z)

/-- The translation is **injective**: distinct codes denote distinct ZF sets. -/
theorem toZF_inj : Function.Injective toZF := by
  intro a b
  induction a using Nat.strong_induction_on generalizing b with
  | _ a IH =>
    intro hab
    apply ext
    intro i
    constructor
    · intro hi
      have h1 : toZF i ∈ toZF a := (mem_toZF a (toZF i)).2 ⟨i, hi, rfl⟩
      rw [hab] at h1
      obtain ⟨c', hc', heq⟩ := (mem_toZF b (toZF i)).1 h1
      have : i = c' := IH i (testBit_lt a i hi) heq.symm
      rw [this]; exact hc'
    · intro hi
      have h1 : toZF i ∈ toZF b := (mem_toZF b (toZF i)).2 ⟨i, hi, rfl⟩
      rw [← hab] at h1
      obtain ⟨c', hc', heq⟩ := (mem_toZF a (toZF i)).1 h1
      have : c' = i := IH c' (testBit_lt a c' hc') heq
      rw [← this]; exact hc'

/-- **Membership preservation** (the core benchmark fact): encoded membership is
    exactly genuine `∈` in the ZF universe. -/
theorem toZF_mem_toZF (a b : ℕ) : toZF a ∈ toZF b ↔ Mem a b := by
  rw [mem_toZF]
  constructor
  · rintro ⟨a', ha', heq⟩; rwa [toZF_inj heq] at ha'
  · intro h; exact ⟨a, h, rfl⟩

/-- The von Neumann successor on codes corresponds to `s ↦ insert s s` on ZF sets. -/
theorem toZF_succ (n : ℕ) : toZF (succ n) = insert (toZF n) (toZF n) := by
  apply ZFSet.ext; intro z
  rw [mem_toZF, ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_succ] at ha
    rcases ha with rfl | ha
    · exact Or.inl rfl
    · exact Or.inr ((mem_toZF n (toZF a)).2 ⟨a, ha, rfl⟩)
  · rintro (rfl | hz)
    · exact ⟨n, self_mem_succ n, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := (mem_toZF n z).1 hz
      exact ⟨a, mem_succ_of_mem ha, rfl⟩

/-! ## The hereditarily finite predicate -/

/-- A ZF set is **hereditarily finite** if it is finite and all of its elements
    are hereditarily finite.  This is the textbook definition of the HF universe. -/
def IsHF (x : ZFSet) : Prop := ZFSet.Hereditarily (fun s => Set.Finite {y | y ∈ s}) x

theorem isHF_iff {x : ZFSet} : IsHF x ↔ Set.Finite {y | y ∈ x} ∧ ∀ y ∈ x, IsHF y :=
  ZFSet.hereditarily_iff

theorem IsHF.finite {x : ZFSet} (h : IsHF x) : Set.Finite {y | y ∈ x} := (isHF_iff.1 h).1

theorem IsHF.mem {x y : ZFSet} (h : IsHF x) (hy : y ∈ x) : IsHF y := (isHF_iff.1 h).2 y hy

/-! ## Closure of HF under the ZF − Infinity operations -/

theorem hf_empty : IsHF (∅ : ZFSet) := by
  rw [isHF_iff]
  refine ⟨?_, ?_⟩
  · have : {y : ZFSet | y ∈ (∅ : ZFSet)} = ∅ := by
      ext y; simp [ZFSet.notMem_empty]
    rw [this]; exact Set.finite_empty
  · intro y hy; exact absurd hy (ZFSet.notMem_empty y)

/-
**Closure of HF under `insert`** (yields Pairing).
-/
theorem hf_insert {a b : ZFSet} (ha : IsHF a) (hb : IsHF b) : IsHF (insert a b) := by
  -- Apply the definition of `IsHF` to `insert a b`.
  rw [isHF_iff];
  refine' ⟨ _, _ ⟩;
  · convert Set.Finite.insert a ( hb.finite ) using 1;
    ext; simp [ZFSet.mem_insert_iff];
  · intro y hy; rw [ZFSet.mem_insert_iff] at hy; rcases hy with ( rfl | hy ) <;> [ exact ha; exact hb.mem hy ] ;

/-
**Closure of HF under union** `⋃₀`.
-/
theorem hf_sUnion {a : ZFSet} (ha : IsHF a) : IsHF (⋃₀ a) := by
  rw [isHF_iff] at *;
  simp +decide [ ZFSet.mem_sUnion ];
  exact ⟨ Set.Finite.subset ( Set.Finite.biUnion ha.1 fun x hx => ( ha.2 x hx ).finite ) fun y hy => by aesop, fun y x hx hy => ( ha.2 x hx ).mem hy ⟩

/-
**Closure of HF under power set**.
-/
theorem hf_powerset {a : ZFSet} (ha : IsHF a) : IsHF a.powerset := by
  -- First, part (1): `{c | c ∈ a.powerset}` is finite.
  -- By `ZFSet.mem_powerset`, `{c | c ∈ a.powerset} = {c | c ⊆ a}`.
  have hf_powerset0 : Set.Finite {c | c ⊆ a} := by
    -- Consider the map `g : ZFSet → Set ZFSet`, `g c = {y | y ∈ c}`. On `{c | c ⊆ a}` this map is injective by extensionality (`ZFSet.ext`: if `{y|y∈c₁} = {y|y∈c₂}` then `c₁ = c₂`).
    have hg_inj : Set.InjOn (fun c : ZFSet => {y | y ∈ c}) {c : ZFSet | c ⊆ a} := by
      intro c hc d hd hcd; ext y; aesop;
    convert Set.Finite.of_finite_image ( Set.Finite.subset ( Set.Finite.powerset ( ha.finite ) ) ?_ ) hg_inj using 1;
    exact Set.image_subset_iff.mpr fun c hc => fun y hy => hc hy;
  -- Every `c ⊆ a` is `IsHF`.
  have hf_powerset1 : ∀ c, c ⊆ a → IsHF c := by
    intro c hc; rw [ isHF_iff ] at *; simp_all +decide ;
    exact ⟨ ha.1.subset fun x hx => hc hx, fun y hy => ha.2 y <| hc hy ⟩;
  rw [ isHF_iff ];
  simp_all +decide [ ZFSet.mem_powerset ]

/-
**Closure of HF under separation**.
-/
theorem hf_sep {a : ZFSet} (ha : IsHF a) (p : ZFSet → Prop) : IsHF (ZFSet.sep p a) := by
  rw [isHF_iff] at *;
  refine' ⟨ _, _ ⟩;
  · exact ha.1.subset fun x hx => by simp at hx; exact hx.1;
  · exact fun y hy => ha.2 y <| ZFSet.mem_sep.mp hy |>.1

/-
**Closure of HF under (definable) replacement**: the image of an HF set under
    a function sending HF sets to HF sets is HF.
-/
theorem hf_image {a : ZFSet} (ha : IsHF a) (f : ZFSet → ZFSet) [ZFSet.Definable₁ f]
    (hf : ∀ c ∈ a, IsHF (f c)) : IsHF (ZFSet.image f a) := by
  rw [isHF_iff] at *;
  refine' ⟨ _, _ ⟩;
  · convert ha.1.image f using 1;
    ext; simp [ZFSet.mem_image];
  · intro y hy; rw [ZFSet.mem_image] at hy; obtain ⟨x, hx, rfl⟩ := hy; exact hf x hx;

/-! ## The first eight ZF axioms, in literal `ZFSet` language, for `HF` -/

/-- **(1) Extensionality** for HF (inherited from the genuine ZF universe). -/
theorem zf_extensionality {a b : ZFSet} (_ha : IsHF a) (_hb : IsHF b)
    (h : ∀ c, c ∈ a ↔ c ∈ b) : a = b := ZFSet.ext h

/-- **(2) Empty set** for HF. -/
theorem zf_empty : IsHF (∅ : ZFSet) ∧ ∀ c, c ∉ (∅ : ZFSet) :=
  ⟨hf_empty, fun c => ZFSet.notMem_empty c⟩

/-- **(3) Pairing** for HF. -/
theorem zf_pairing {a b : ZFSet} (ha : IsHF a) (hb : IsHF b) :
    ∃ z, IsHF z ∧ ∀ c, c ∈ z ↔ (c = a ∨ c = b) := by
  refine ⟨insert a (insert b ∅), hf_insert ha (hf_insert hb hf_empty), fun c => ?_⟩
  rw [ZFSet.mem_insert_iff, ZFSet.mem_insert_iff]
  simp [ZFSet.notMem_empty]

/-- **(4) Union** for HF. -/
theorem zf_union {a : ZFSet} (ha : IsHF a) :
    ∃ z, IsHF z ∧ ∀ c, c ∈ z ↔ ∃ y, y ∈ a ∧ c ∈ y := by
  refine ⟨⋃₀ a, hf_sUnion ha, fun c => ?_⟩
  rw [ZFSet.mem_sUnion]

/-- **(5) Power set** for HF. -/
theorem zf_powerset {a : ZFSet} (ha : IsHF a) :
    ∃ z, IsHF z ∧ ∀ c, c ∈ z ↔ c ⊆ a :=
  ⟨a.powerset, hf_powerset ha, fun _ => ZFSet.mem_powerset⟩

/-- **(6) Separation** for HF. -/
theorem zf_separation {a : ZFSet} (ha : IsHF a) (p : ZFSet → Prop) :
    ∃ z, IsHF z ∧ ∀ c, c ∈ z ↔ (c ∈ a ∧ p c) :=
  ⟨ZFSet.sep p a, hf_sep ha p, fun _ => ZFSet.mem_sep⟩

/-- **(7) Replacement** for HF: the HF image of an HF set under a definable map
    sending HF sets to HF sets is HF. -/
theorem zf_replacement {a : ZFSet} (ha : IsHF a) (f : ZFSet → ZFSet) [ZFSet.Definable₁ f]
    (hf : ∀ c ∈ a, IsHF (f c)) :
    ∃ z, IsHF z ∧ ∀ c, c ∈ z ↔ ∃ y, y ∈ a ∧ f y = c :=
  ⟨ZFSet.image f a, hf_image ha f hf, fun _ => ZFSet.mem_image⟩

/-- **(8) Foundation** for HF (inherited from the genuine ZF universe). -/
theorem zf_foundation {a : ZFSet} (_ha : IsHF a) (hne : a ≠ ∅) :
    ∃ y, y ∈ a ∧ ∀ z, z ∈ y → z ∉ a := by
  obtain ⟨y, hy, hmin⟩ := ZFSet.regularity a hne
  refine ⟨y, hy, ?_⟩
  intro z hz hza
  have : z ∈ a ∩ y := ZFSet.mem_inter.2 ⟨hza, hz⟩
  rw [hmin] at this
  exact ZFSet.notMem_empty z this

/-! ## The HF characterization: `range toZF = HF` -/

/-- The set of elements of `toZF n` is finite. -/
theorem toZF_elems_finite (n : ℕ) : Set.Finite {y | y ∈ toZF n} := by
  have heq : {y | y ∈ toZF n} = toZF '' {a | Mem a n} := by
    ext y; simp only [Set.mem_setOf_eq, Set.mem_image]; rw [mem_toZF]
  rw [heq]
  have hsub : {a | Mem a n} ⊆ Set.Iio n := fun a ha => testBit_lt n a ha
  exact (Set.Finite.subset (Set.finite_Iio n) hsub).image toZF

/-- **Range ⊆ HF**: every translated code is a hereditarily finite set. -/
theorem isHF_toZF (n : ℕ) : IsHF (toZF n) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rw [IsHF, ZFSet.hereditarily_iff]
    refine ⟨toZF_elems_finite n, ?_⟩
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (mem_toZF n y).1 hy
    exact IH a (testBit_lt n a ha)

/-
**HF ⊆ Range**: every hereditarily finite ZF set is the translation of a code.

    Proof by `∈`-induction (`ZFSet.inductionOn`).  Given `IsHF x`, consider the set
    of codes `S' = {n | toZF n ∈ x}`.  Its `toZF`-image is contained in the finite
    set `x` and `toZF` is injective, so `S'` is finite; let `s = S'.toFinset` and
    `m = code s`.  Then `z ∈ toZF m ↔ ∃ a ∈ s, toZF a = z`, i.e. `↔ ∃ a, toZF a ∈ x
    ∧ toZF a = z`.  The forward direction gives `z ∈ x`; conversely, for `z ∈ x`
    the induction hypothesis (`IsHF.mem`) provides a code `a` with `toZF a = z`, and
    then `toZF a ∈ x`.  Hence `toZF m = x` by extensionality.
-/
theorem exists_code_of_isHF (x : ZFSet) (hx : IsHF x) : ∃ n, toZF n = x := by
  induction' x using ZFSet.inductionOn with x ih;
  -- Consider the set of codes `S' := {n : ℕ | toZF n ∈ x}`.
  set S' : Set ℕ := {n | toZF n ∈ x} with hS';
  -- Since `toZF` is injective, `S'` is finite.
  have hS'_finite : S'.Finite := by
    have hS'_finite : (Set.image toZF S').Finite := by
      exact Set.Finite.subset ( hx.finite ) ( Set.image_subset_iff.mpr fun n hn => hn );
    exact Set.Finite.of_finite_image hS'_finite ( toZF_inj.injOn );
  -- Let `m := code s`. We claim `toZF m = x`.
  obtain ⟨m, hm⟩ : ∃ m, toZF m = x := by
    have h_image : ∀ z, z ∈ toZF (code hS'_finite.toFinset) ↔ ∃ a, toZF a ∈ x ∧ toZF a = z := by
      intro z; rw [mem_toZF]; constructor <;> intro hz <;> simp_all +decide [ mem_code ] ;
    refine' ⟨ _, ZFSet.ext fun z => _ ⟩;
    exact code hS'_finite.toFinset;
    constructor <;> intro hz;
    · grind;
    · exact h_image z |>.2 <| by obtain ⟨ n, rfl ⟩ := ih z hz ( hx.mem hz ) ; exact ⟨ n, by aesop ⟩ ;
  use m

theorem isHF_iff_exists_code {x : ZFSet} : IsHF x ↔ ∃ n, toZF n = x :=
  ⟨exists_code_of_isHF x, by rintro ⟨n, rfl⟩; exact isHF_toZF n⟩

/-- **`Univ` is the standard HF universe** (code form): the range of the
    translation is exactly the hereditarily finite sets. -/
theorem range_toZF_eq_isHF : Set.range toZF = {x | IsHF x} := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩; exact isHF_toZF n
  · intro hx; exact exists_code_of_isHF x hx

/-! ## The Axiom of Infinity, benchmarked against `IsInductiveSet` -/

/-- **The standard (textbook) definition of an inductive set**: it contains the
    empty set and is closed under the von Neumann successor `y ↦ y ∪ {y} =
    insert y y`.  The Axiom of Infinity asserts the existence of such a set. -/
def IsInductiveSet (z : ZFSet) : Prop := ∅ ∈ z ∧ ∀ y ∈ z, insert y y ∈ z

/-- **The Axiom of Infinity is TRUE in the full ZF universe**: `ZFSet.omega` is an
    inductive set.  (This is the consistency / non-triviality side of the
    benchmark: Infinity is a genuine axiom, satisfied by the standard universe.) -/
theorem exists_isInductiveSet : ∃ z, IsInductiveSet z :=
  ⟨ZFSet.omega, ZFSet.omega_zero, fun _ hy => ZFSet.omega_succ hy⟩

/-- The internal `Inductive` predicate on a code matches the standard
    `IsInductiveSet` on its translation. -/
theorem isInductiveSet_toZF_iff (z : ℕ) : IsInductiveSet (toZF z) ↔ Inductive z := by
  constructor
  · rintro ⟨h0, hsucc⟩
    refine ⟨?_, ?_⟩
    · have e0 : toZF 0 ∈ toZF z := by rw [toZF_zero]; exact h0
      exact (toZF_mem_toZF 0 z).1 e0
    · intro y hy
      have hyZ : toZF y ∈ toZF z := (toZF_mem_toZF y z).2 hy
      have hsy := hsucc (toZF y) hyZ
      rw [← toZF_succ] at hsy
      exact (toZF_mem_toZF (succ y) z).1 hsy
  · rintro ⟨h0, hsucc⟩
    refine ⟨?_, ?_⟩
    · have e0 : toZF 0 ∈ toZF z := (toZF_mem_toZF 0 z).2 h0
      rw [toZF_zero] at e0; exact e0
    · intro Y hY
      obtain ⟨a, ha, rfl⟩ := (mem_toZF z Y).1 hY
      rw [← toZF_succ]
      exact (toZF_mem_toZF (succ a) z).2 (hsucc a ((toZF_mem_toZF a z).1
        ((mem_toZF z (toZF a)).2 ⟨a, ha, rfl⟩)))

/-- **The Axiom of Infinity strictly FAILS on HF**: no hereditarily finite set is
    inductive.  This is exactly the negation of the textbook Infinity axiom,
    relativized to the HF universe — making `no_inductive_set` a genuine refutation
    of the standard axiom, not of some non-standard surrogate. -/
theorem no_inductiveSet_HF : ¬ ∃ z : ZFSet.{0}, IsHF z ∧ IsInductiveSet z := by
  rintro ⟨z, hz, hind⟩
  obtain ⟨n, rfl⟩ := isHF_iff_exists_code.1 hz
  exact no_inductive_set ⟨n, (isInductiveSet_toZF_iff n).1 hind⟩

/-! ## Transporting the translation through the RGF reals -/

open Classical in
/-- The translation of an RGF real that codes a set, into the genuine ZF universe.
    (Reals outside `Univ` are sent to `∅`.) -/
noncomputable def transZF (x : RGFReal') : ZFSet :=
  if h : x ∈ Univ then toZF h.choose else ∅

/-- On the carrier `Univ`, `transZF` agrees with `toZF` on the underlying code. -/
theorem transZF_RVal (n : ℕ) : transZF (RVal n) = toZF n := by
  have h : RVal n ∈ Univ := RVal_mem_univ n
  rw [transZF, dif_pos h]
  congr 1
  exact RVal_injective h.choose_spec

/-- **Membership preservation through the reals**: `RMem` corresponds to genuine
    `∈` in the ZF universe via `transZF`. -/
theorem transZF_preserves_mem {x y : RGFReal'} (hx : x ∈ Univ) (hy : y ∈ Univ) :
    RMem x y ↔ transZF x ∈ transZF y := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  rw [transZF_RVal, transZF_RVal, RMem_RVal, toZF_mem_toZF]

/-- **`Univ` maps onto the standard HF universe**: the `transZF`-image of `Univ`
    is exactly the hereditarily finite sets. -/
theorem transZF_image_univ_eq_isHF : transZF '' Univ = {x | IsHF x} := by
  ext x
  constructor
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
    rw [transZF_RVal]; exact isHF_toZF n
  · intro hx
    obtain ⟨n, rfl⟩ := isHF_iff_exists_code.1 hx
    exact ⟨RVal n, RVal_mem_univ n, transZF_RVal n⟩

end RGFSet
end RGF