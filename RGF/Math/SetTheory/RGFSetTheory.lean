/-
  Foundations/RGFSetTheory.lean

  **The RGF reals carry the whole (hereditarily finite) set-theoretic universe.**

  This file shows that the generative reals `RGFReal'` are not merely a copy of an
  ordered field: they host an entire model of set theory.  Concretely we use the
  *Ackermann encoding* — a natural number `n` is read as the set of those `a` with
  the `a`-th binary digit of `n` set (`Nat.testBit n a`).  This makes `(ℕ, ∈ₐ)` a
  model of all the axioms of Zermelo–Fraenkel set theory **except Infinity**, i.e.
  exactly the universe `HF` of hereditarily finite sets.  We then transport this
  membership structure faithfully onto a subset of `RGFReal'` through the canonical
  embedding `RVal : ℕ → RGFReal'`, `n ↦ ofReal n`.

  Honest scope.  The *full* proper-class universe `V` of ZF cannot live inside any
  single set such as `ℝ` (cardinality / Russell-style obstructions), so the
  faithful statement is: the reals carry the hereditarily finite universe `HF`,
  which already validates Extensionality, Empty set, Pairing, Union, **Power set**,
  the **Separation** schema, the **Replacement** schema, and Foundation.  (The
  Infinity axiom genuinely *fails* in `HF`; we record this honestly as
  `not_infinity`.)

  All set operations, the power-set operation, and the replacement schema are thus
  encoded by, and provable for, the RGF reals.
-/
import Mathlib
import RGF.Math.Real.RGFRealExamples

namespace RGF
namespace RGFSet

open RGFReal'

/-! ## The Ackermann membership relation on ℕ -/

/-- Ackermann membership: `a ∈ₐ b` iff the `a`-th binary digit of `b` is set. -/
def Mem (a b : ℕ) : Prop := Nat.testBit b a = true

@[inherit_doc] scoped infix:50 " ∈ₐ " => Mem

instance (a b : ℕ) : Decidable (Mem a b) := by unfold Mem; infer_instance

/-- The (finite) set of elements of the code `n`. -/
def elems (n : ℕ) : Finset ℕ := (Finset.range n).filter (fun i => Nat.testBit n i)

/-- The code of a finite set of naturals: `∑ j ∈ s, 2 ^ j`. -/
def code (s : Finset ℕ) : ℕ := s.sum (fun j => 2 ^ j)

theorem testBit_lt (n i : ℕ) (h : Nat.testBit n i = true) : i < n := by
  have h2 : 2 ^ i ≤ n := Nat.ge_two_pow_of_testBit h
  have : i < 2 ^ i := Nat.lt_two_pow_self
  omega

theorem mem_elems (n i : ℕ) : i ∈ elems n ↔ Nat.testBit n i = true := by
  unfold elems
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨testBit_lt n i h, h⟩

/-
`code` realizes the prescribed bits: bit `i` of `code s` is set iff `i ∈ s`.
-/
theorem testBit_code (s : Finset ℕ) (i : ℕ) : Nat.testBit (code s) i = true ↔ i ∈ s := by
  induction' s using Finset.induction with a s ha ih generalizing i ; simp_all +decide [ code ];
  -- By definition of `code`, we have `code (insert a s) = 2^a + code s`.
  have h_code_insert : code (insert a s) = 2^a + code s := by
    unfold code; rw [ Finset.sum_insert ha ] ;
  -- By definition of `code`, we have `code s &&& 2^a = 0`.
  have h_code_s_and_two_pow_a : code s &&& 2^a = 0 := by
    refine' Nat.eq_of_testBit_eq _;
    grind;
  -- By definition of `code`, we have `code s + 2^a = code s ||| 2^a`.
  have h_code_s_plus_two_pow_a : code s + 2^a = code s ||| 2^a := by
    have h_code_s_plus_two_pow_a : ∀ x y : ℕ, x &&& y = 0 → x + y = x ||| y := by
      intros x y hxy
      induction' x using Nat.binaryRec with x ih generalizing y <;> induction' y using Nat.binaryRec with y ih' <;> simp_all +decide;
      cases x <;> cases y <;> simp_all +decide [ Nat.bit ]; all_goals grind;
    exact h_code_s_plus_two_pow_a _ _ h_code_s_and_two_pow_a;
  grind

theorem code_elems (n : ℕ) : code (elems n) = n := by
  convert Nat.eq_of_testBit_eq ( fun i => ?_ ) using 1;
  have := testBit_code ( elems n ) i; have := mem_elems n i; aesop;

theorem elems_code (s : Finset ℕ) : elems (code s) = s := by
  ext i; simp only [mem_elems]
  convert testBit_code s i using 1

/-- Membership into a coded set is just Finset membership. -/
theorem mem_code (c : ℕ) (s : Finset ℕ) : Mem c (code s) ↔ c ∈ s := by
  unfold Mem; rw [testBit_code]

/-! ## The ZF axioms (minus Infinity), proved for `(ℕ, ∈ₐ)` -/

/-- **Empty set.** `0` codes the empty set. -/
theorem empty (a : ℕ) : ¬ Mem a 0 := by
  unfold Mem; simp [Nat.zero_testBit]

/-- **Extensionality.** -/
theorem ext {a b : ℕ} (h : ∀ c, Mem c a ↔ Mem c b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := h i
  unfold Mem at this
  rcases Bool.eq_false_or_eq_true (Nat.testBit a i) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (Nat.testBit b i) with hb | hb <;>
    simp_all

/-- **Pairing.** -/
theorem pairing (x y : ℕ) : ∃ z, ∀ c, Mem c z ↔ (c = x ∨ c = y) := by
  refine ⟨code {x, y}, fun c => ?_⟩
  rw [mem_code]; simp [Finset.mem_insert]

/-- **Union.** -/
theorem union (x : ℕ) : ∃ z, ∀ c, Mem c z ↔ ∃ y, Mem y x ∧ Mem c y := by
  refine ⟨code ((elems x).biUnion elems), fun c => ?_⟩
  rw [mem_code, Finset.mem_biUnion]
  constructor
  · rintro ⟨y, hy, hc⟩
    exact ⟨y, (mem_elems x y).1 hy, (mem_elems y c).1 hc⟩
  · rintro ⟨y, hy, hc⟩
    exact ⟨y, (mem_elems x y).2 hy, (mem_elems y c).2 hc⟩

/-- **Power set.** -/
theorem powerset (x : ℕ) :
    ∃ z, ∀ c, Mem c z ↔ (∀ d, Mem d c → Mem d x) := by
  refine ⟨code ((elems x).powerset.image code), fun c => ?_⟩
  rw [mem_code, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩ d hd
    rw [Finset.mem_powerset] at ht
    rw [mem_code] at hd
    exact (mem_elems x d).1 (ht hd)
  · intro h
    refine ⟨elems c, ?_, code_elems c⟩
    rw [Finset.mem_powerset]
    intro d hd
    exact (mem_elems x d).2 (h d ((mem_elems c d).1 hd))

/-- **Separation schema.** -/
theorem separation (x : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ∃ z, ∀ c, Mem c z ↔ (Mem c x ∧ p c) := by
  refine ⟨code ((elems x).filter p), fun c => ?_⟩
  rw [mem_code, Finset.mem_filter, mem_elems]; rfl

/-- **Replacement schema.** -/
theorem replacement (x : ℕ) (f : ℕ → ℕ) :
    ∃ z, ∀ c, Mem c z ↔ ∃ y, Mem y x ∧ c = f y := by
  classical
  refine ⟨code ((elems x).image f), fun c => ?_⟩
  rw [mem_code, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, (mem_elems x y).1 hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, (mem_elems x y).2 hy, rfl⟩

/-
**Foundation / Regularity.**
-/
theorem foundation (x : ℕ) (hx : x ≠ 0) :
    ∃ y, Mem y x ∧ ∀ z, Mem z y → ¬ Mem z x := by
  obtain ⟨y, hy⟩ : ∃ y, y ∈ elems x ∧ ∀ z, z ∈ elems x → y ≤ z := by
    apply_rules [ Finset.exists_min_image ];
    contrapose! hx;
    rw [ ← code_elems x, hx, code ] ; simp +decide;
  refine' ⟨ y, _, _ ⟩;
  · exact mem_elems x y |>.1 hy.1;
  · intro z hz;
    exact fun h => not_lt_of_ge ( hy.2 z ( by simpa [ mem_elems ] using h ) ) ( testBit_lt _ _ hz )

/-! ## Infinity fails: this is genuinely the *finite* universe -/

/-
**Infinity is false** in the Ackermann model: there is no inductive set.
    This makes precise that the reals carry exactly the hereditarily finite
    universe `HF` (a model of ZF − Infinity).
-/
theorem not_infinity :
    ¬ ∃ z, Mem 0 z ∧ ∀ y, Mem y z →
        ∃ w, Mem w z ∧ ∀ c, Mem c w ↔ (c = y ∨ Mem c y) := by
  -- By induction, we can show that for all n, g n is in z.
  have h_g_in_z : ∀ z : ℕ, Mem 0 z → (∀ y : ℕ, Mem y z → ∃ w : ℕ, Mem w z ∧ ∀ c : ℕ, Mem c w ↔ c = y ∨ Mem c y) → ∀ n : ℕ, ∃ g_n : ℕ, Mem g_n z ∧ n ≤ g_n := by
    intros z hz h_ind n
    induction' n with n ih;
    · exact ⟨ 0, hz, Nat.zero_le _ ⟩;
    · obtain ⟨ g_n, hg_n₁, hg_n₂ ⟩ := ih; obtain ⟨ w, hw₁, hw₂ ⟩ := h_ind g_n hg_n₁; use w; simp_all +decide [ Mem ] ;
      exact lt_of_le_of_lt hg_n₂ ( testBit_lt _ _ ( hw₂ _ |>.2 ( Or.inl rfl ) ) );
  intro ⟨ z, hz₁, hz₂ ⟩ ; specialize h_g_in_z z hz₁ hz₂ ( z + 1 ) ; obtain ⟨ g_n, hg_n₁, hg_n₂ ⟩ := h_g_in_z ; linarith [ testBit_lt _ _ hg_n₁ ] ;

/-! ## Carrying the universe inside the RGF reals -/

/-- The embedding of set codes into the generative reals. -/
noncomputable def RVal (n : ℕ) : RGFReal' := RGFReal'.ofReal (n : ℝ)

/-- Membership transported onto the reals: `x ∈ y` for reals coding sets. -/
def RMem (x y : RGFReal') : Prop := ∃ m n : ℕ, x = RVal m ∧ y = RVal n ∧ Mem m n

/-- The set-theoretic universe carried by the RGF reals. -/
def Univ : Set RGFReal' := Set.range RVal

theorem RVal_injective : Function.Injective RVal := by
  intro a b h
  unfold RVal at h
  have := congrArg toReal h
  simpa using this

@[simp] theorem RVal_mem_univ (n : ℕ) : RVal n ∈ Univ := ⟨n, rfl⟩

/-- The bridge: transported membership between codes is Ackermann membership. -/
theorem RMem_RVal (m n : ℕ) : RMem (RVal m) (RVal n) ↔ Mem m n := by
  constructor
  · rintro ⟨m', n', hm, hn, h⟩
    rw [RVal_injective hm, RVal_injective hn]; exact h
  · intro h; exact ⟨m, n, rfl, rfl, h⟩

/-! ### The ZF axioms (minus Infinity), carried by the RGF reals -/

/-- **Extensionality**, carried by the reals. -/
theorem real_extensionality {a b : RGFReal'} (ha : a ∈ Univ) (hb : b ∈ Univ)
    (h : ∀ c ∈ Univ, RMem c a ↔ RMem c b) : a = b := by
  obtain ⟨na, rfl⟩ := ha
  obtain ⟨nb, rfl⟩ := hb
  have : na = nb := by
    apply ext
    intro c
    have := h (RVal c) (RVal_mem_univ c)
    rwa [RMem_RVal, RMem_RVal] at this
  rw [this]

/-- **Empty set**, carried by the reals. -/
theorem real_empty : ∃ e ∈ Univ, ∀ c ∈ Univ, ¬ RMem c e := by
  refine ⟨RVal 0, RVal_mem_univ 0, ?_⟩
  rintro c ⟨n, rfl⟩
  rw [RMem_RVal]; exact empty n

/-- **Pairing**, carried by the reals. -/
theorem real_pairing (x y : RGFReal') (hx : x ∈ Univ) (hy : y ∈ Univ) :
    ∃ z ∈ Univ, ∀ c ∈ Univ, RMem c z ↔ (c = x ∨ c = y) := by
  obtain ⟨nx, rfl⟩ := hx
  obtain ⟨ny, rfl⟩ := hy
  obtain ⟨z, hz⟩ := pairing nx ny
  refine ⟨RVal z, RVal_mem_univ z, ?_⟩
  rintro c ⟨nc, rfl⟩
  rw [RMem_RVal, hz]
  constructor
  · rintro (h | h) <;> [left; right] <;> rw [h]
  · rintro (h | h) <;> [left; right] <;> exact RVal_injective h

/-- **Union**, carried by the reals. -/
theorem real_union (x : RGFReal') (hx : x ∈ Univ) :
    ∃ z ∈ Univ, ∀ c ∈ Univ, RMem c z ↔ ∃ y ∈ Univ, RMem y x ∧ RMem c y := by
  obtain ⟨nx, rfl⟩ := hx
  obtain ⟨z, hz⟩ := union nx
  refine ⟨RVal z, RVal_mem_univ z, ?_⟩
  rintro c ⟨nc, rfl⟩
  rw [RMem_RVal, hz]
  constructor
  · rintro ⟨y, hy, hc⟩
    exact ⟨RVal y, RVal_mem_univ y, (RMem_RVal y nx).2 hy, (RMem_RVal nc y).2 hc⟩
  · rintro ⟨y, ⟨ny, rfl⟩, hy, hc⟩
    rw [RMem_RVal] at hy hc
    exact ⟨ny, hy, hc⟩

/-- **Power set**, carried by the reals. -/
theorem real_powerset (x : RGFReal') (hx : x ∈ Univ) :
    ∃ z ∈ Univ, ∀ c ∈ Univ, RMem c z ↔ (∀ d ∈ Univ, RMem d c → RMem d x) := by
  obtain ⟨nx, rfl⟩ := hx
  obtain ⟨z, hz⟩ := powerset nx
  refine ⟨RVal z, RVal_mem_univ z, ?_⟩
  rintro c ⟨nc, rfl⟩
  rw [RMem_RVal, hz]
  constructor
  · rintro h d ⟨nd, rfl⟩ hd
    rw [RMem_RVal] at hd ⊢
    exact h nd hd
  · intro h d hd
    have := h (RVal d) (RVal_mem_univ d)
    rw [RMem_RVal, RMem_RVal] at this
    exact this hd

/-- **Separation schema**, carried by the reals. -/
theorem real_separation (x : RGFReal') (hx : x ∈ Univ) (p : RGFReal' → Prop) :
    ∃ z ∈ Univ, ∀ c ∈ Univ, RMem c z ↔ (RMem c x ∧ p c) := by
  classical
  obtain ⟨nx, rfl⟩ := hx
  obtain ⟨z, hz⟩ := separation nx (fun n => p (RVal n))
  refine ⟨RVal z, RVal_mem_univ z, ?_⟩
  rintro c ⟨nc, rfl⟩
  rw [RMem_RVal, hz, RMem_RVal]

/-
**Replacement schema**, carried by the reals.
-/
theorem real_replacement (x : RGFReal') (hx : x ∈ Univ) (f : RGFReal' → RGFReal')
    (hf : ∀ c ∈ Univ, f c ∈ Univ) :
    ∃ z ∈ Univ, ∀ c ∈ Univ, RMem c z ↔ ∃ y ∈ Univ, RMem y x ∧ c = f y := by
  obtain ⟨ nx, rfl ⟩ := hx;
  -- By definition of $f$, for each $n$, there exists $m$ such that $f (RVal n) = RVal m$.
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, ∀ n, f (RVal n) = RVal (g n) := by
    exact ⟨ fun n => Classical.choose ( hf _ ( RVal_mem_univ n ) ), fun n => Eq.symm ( Classical.choose_spec ( hf _ ( RVal_mem_univ n ) ) ) ⟩;
  obtain ⟨ z, hz ⟩ := replacement nx g;
  refine' ⟨ RVal z, RVal_mem_univ _, fun c hc => _ ⟩ ; rcases hc with ⟨ nc, rfl ⟩ ; simp +decide [ RMem_RVal, hz ] ;
  constructor;
  · rintro ⟨ y, hy, rfl ⟩ ; exact ⟨ RVal y, RVal_mem_univ y, by simp +decide [ RMem_RVal, hy ], by simp +decide [ hg ] ⟩ ;
  · rintro ⟨ y, ⟨ ny, rfl ⟩, hy, h ⟩ ; use ny; simp_all +decide [ RMem_RVal ] ;
    exact RVal_injective h

/-- **Foundation**, carried by the reals. -/
theorem real_foundation (x : RGFReal') (hx : x ∈ Univ)
    (hne : ∃ c ∈ Univ, RMem c x) :
    ∃ y ∈ Univ, RMem y x ∧ ∀ z ∈ Univ, RMem z y → ¬ RMem z x := by
  obtain ⟨nx, rfl⟩ := hx
  obtain ⟨c, ⟨nc, rfl⟩, hc⟩ := hne
  rw [RMem_RVal] at hc
  have hx0 : nx ≠ 0 := by
    rintro rfl; exact empty nc hc
  obtain ⟨y, hy, hmin⟩ := foundation nx hx0
  refine ⟨RVal y, RVal_mem_univ y, (RMem_RVal y nx).2 hy, ?_⟩
  rintro z ⟨nz, rfl⟩ hz
  rw [RMem_RVal] at hz ⊢
  exact hmin nz hz

end RGFSet
end RGF