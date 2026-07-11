/-
  Foundations/RGFConsistencyStrength.lean

  **Relative consistency and consistency strength of the RGF set-theoretic core.**

  The companion files `Foundations/RGFSetTheory.lean`, `Foundations/RGFInfinity.lean`
  and `Foundations/RGFZFBenchmark.lean` build, on the Ackermann codes `(ℕ, ∈ₐ)`, a
  model of every Zermelo–Fraenkel axiom *except Infinity* (i.e. the hereditarily
  finite universe `HF`), transported onto the generative reals.  Those results are
  stated *semantically* (predicates `Mem`/`RMem` on a carrier).  This file closes
  the **metamathematical** gap by phrasing them as a genuine *first-order theory*
  and reading off the two facts requested:

  1. **Relative consistency** `Con(ZFC) → Con(RGF)`.  We introduce an honest
     one-sorted first-order language `LMem` with a single binary relation `∈`, write
     the RGF set-theoretic axioms as actual `FirstOrder.Language` sentences
     (Extensionality, Empty set, Pairing, Union, Power set, Foundation, the full
     first-order **Separation** schema, the full first-order **Replacement** schema,
     and the **negation of Infinity**), and bundle them into a theory
     `RGFFinSetTheory`.  The Ackermann structure `(ℕ, ∈ₐ)` satisfies every axiom
     (`ackModel_models`), hence — since that model is built entirely inside Lean's
     type theory (interpretable in ZFC + universes) — the theory is satisfiable
     (`consistency`) and does not prove `⊥` (`not_models_falsum`).  This is exactly
     `Con(ZFC) → Con(RGF)`.

  2. **Consistency strength.**  The theory `RGFFinSetTheory` is precisely
     `ZF − Infinity + ¬Infinity`, i.e. *finite set theory*, the theory of the
     hereditarily-finite universe `HF`.  This sits at the very bottom of the
     consistency hierarchy: it is mutually interpretable with `PA`, strictly weaker
     than full `ZFC` (which proves `Con(PA)` and hence `Con(RGF)`), and far below
     any large-cardinal assumption.  The double Ackermann interpretation is
     recorded as bijections `ackCodeEquiv : ℕ ≃ Finset ℕ` and
     `hfCodeEquiv : ℕ ≃ {x : ZFSet // IsHF x}`, with `ack_mem_iff` / `hfCodeEquiv_mem`
     showing both encodings read off the membership relation faithfully.
-/
import Mathlib
import RGF.Math.SetTheory.RGFZFBenchmark

open FirstOrder Language

namespace RGF
namespace RGFConsistencyStrength

open RGF.RGFSet

/-! ## The honest first-order language of membership -/

/-- The relation symbols of `LMem`: a single binary membership relation. -/
inductive memRel : ℕ → Type
  | mem : memRel 2

/-- The first-order language of membership: no function symbols, one binary
    relation symbol `∈`. -/
def LMem : Language := ⟨fun _ => Empty, memRel⟩

/-- The membership relation symbol. -/
def memSymb : LMem.Relations 2 := memRel.mem

/-- The atomic membership formula `s ∈ t` (over any variable type). -/
def memF {α : Type} (s t : α) : LMem.Formula α :=
  memSymb.formula₂ (Term.var s) (Term.var t)

/-- The atomic equality formula `s = t` (over any variable type). -/
def eqF {α : Type} (s t : α) : LMem.Formula α :=
  Term.equal (Term.var s) (Term.var t)

/-! ## The Ackermann structure `(ℕ, ∈ₐ)` -/

/-- `(ℕ, ∈ₐ)` as an `LMem`-structure: the membership symbol is interpreted as the
    Ackermann membership relation `Mem`. -/
instance ackStructure : LMem.Structure ℕ where
  funMap := fun {_} f => nomatch f
  RelMap := fun {n} r =>
    match n, r with
    | 2, memRel.mem => fun args => Mem (args 0) (args 1)

@[simp] theorem realize_memF {α : Type} (v : α → ℕ) (s t : α) :
    (memF s t).Realize v ↔ Mem (v s) (v t) := by
  unfold memF
  rw [Formula.realize_rel₂]
  simp [memSymb]
  rfl

@[simp] theorem realize_eqF {α : Type} (v : α → ℕ) (s t : α) :
    (eqF s t).Realize v ↔ v s = v t := by
  unfold eqF
  rw [Formula.realize_equal]
  simp

/-! ## The axioms as first-order sentences -/

/-- **Extensionality.** -/
noncomputable def extAx : LMem.Sentence :=
  Formula.iAlls (Fin 2)
    ((Formula.iAlls (Fin 1)
        ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))).iff
         (memF (Sum.inr 0) (Sum.inl (Sum.inr 1))))).imp
     (eqF (Sum.inr 0) (Sum.inr 1)))

/-- **Empty set.** -/
noncomputable def emptyAx : LMem.Sentence :=
  Formula.iExs (Fin 1)
    (Formula.iAlls (Fin 1)
      ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))).not))

/-- **Pairing.** -/
noncomputable def pairingAx : LMem.Sentence :=
  Formula.iAlls (Fin 2)
    (Formula.iExs (Fin 1)
      (Formula.iAlls (Fin 1)
        ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))).iff
         ((eqF (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inr 0)))) ⊔
          (eqF (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inr 1))))))))

/-- **Union.** -/
noncomputable def unionAx : LMem.Sentence :=
  Formula.iAlls (Fin 1)
    (Formula.iExs (Fin 1)
      (Formula.iAlls (Fin 1)
        ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))).iff
         (Formula.iExs (Fin 1)
           ((memF (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))) ⊓
            (memF (Sum.inl (Sum.inr 0)) (Sum.inr 0)))))))

/-- **Power set.** -/
noncomputable def powersetAx : LMem.Sentence :=
  Formula.iAlls (Fin 1)
    (Formula.iExs (Fin 1)
      (Formula.iAlls (Fin 1)
        ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))).iff
         (Formula.iAlls (Fin 1)
           ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))).imp
            (memF (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))))))

/-- **Foundation / Regularity.** -/
noncomputable def foundationAx : LMem.Sentence :=
  Formula.iAlls (Fin 1)
    ((Formula.iExs (Fin 1) (memF (Sum.inr 0) (Sum.inl (Sum.inr 0)))).imp
     (Formula.iExs (Fin 1)
       ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))) ⊓
        (Formula.iAlls (Fin 1)
          ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))).imp
           (memF (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inr 0)))).not)))))

/-- **Axiom of Infinity** (whose *negation* is an axiom of `RGFFinSetTheory`):
    there is a set `z` containing an empty set and closed under von Neumann
    successor. -/
noncomputable def infinityAx : LMem.Sentence :=
  Formula.iExs (Fin 1)
    -- part 1: ∃ e ∈ z, ∀ x, x ∉ e
    ((Formula.iExs (Fin 1)
        ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))) ⊓
         (Formula.iAlls (Fin 1)
           ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))).not))))
     ⊓
     -- part 2: ∀ y ∈ z, ∃ w ∈ z, ∀ c, c ∈ w ↔ (c = y ∨ c ∈ y)
     (Formula.iAlls (Fin 1)
       ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))).imp
        (Formula.iExs (Fin 1)
          ((memF (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inr 0)))) ⊓
           (Formula.iAlls (Fin 1)
             ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))).iff
              ((eqF (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inr 0)))) ⊔
               (memF (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inr 0))))))))))))

/-- **Separation schema instance** for a first-order formula `φ` with `n`
    parameters and one separated variable (the `Fin 1` slot):
    `∀ params, ∀ a, ∃ b, ∀ x, (x ∈ b ↔ x ∈ a ∧ φ)`. -/
noncomputable def sepInstance (n : ℕ) (φ : LMem.Formula (Fin n ⊕ Fin 1)) :
    LMem.Sentence :=
  let g : (Fin n ⊕ Fin 1) → ((((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) :=
    fun z => match z with
      | Sum.inl i => Sum.inl (Sum.inl (Sum.inl (Sum.inr i)))
      | Sum.inr _ => Sum.inr 0
  let x : ((((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) := Sum.inr 0
  let b : ((((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) := Sum.inl (Sum.inr 0)
  let a : ((((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) :=
    Sum.inl (Sum.inl (Sum.inr 0))
  let matrix : LMem.Formula ((((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) :=
    (memF x b).iff ((memF x a) ⊓ (Formula.relabel g φ))
  Formula.iAlls (Fin n)
    (Formula.iAlls (Fin 1) (Formula.iExs (Fin 1) (Formula.iAlls (Fin 1) matrix)))

/-- Relabelling map placing `φ`'s parameters and its input/output slots into the
    context of the functional-hypothesis matrix (after `∀ u, ∃ v`). -/
def gReplFun (n : ℕ) : (Fin n ⊕ Fin 2) → (((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1) :=
  fun z => match z with
    | Sum.inl i => Sum.inl (Sum.inl (Sum.inr i))
    | Sum.inr j => if j = 0 then Sum.inl (Sum.inr 0) else Sum.inr 0

/-- Relabelling map for the uniqueness clause of the functional hypothesis
    (after `∀ u, ∃ v, ∀ w`). -/
def gReplFun2 (n : ℕ) : (Fin n ⊕ Fin 2) → ((((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) :=
  fun z => match z with
    | Sum.inl i => Sum.inl (Sum.inl (Sum.inl (Sum.inr i)))
    | Sum.inr j => if j = 0 then Sum.inl (Sum.inl (Sum.inr 0)) else Sum.inr 0

/-- Relabelling map for the image-defining clause (after `∀ a, ∃ b, ∀ v, ∃ u`). -/
def gReplMain (n : ℕ) :
    (Fin n ⊕ Fin 2) → (((((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) :=
  fun z => match z with
    | Sum.inl i => Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr i))))
    | Sum.inr j => if j = 0 then Sum.inr 0 else Sum.inl (Sum.inr 0)

@[simp] theorem comp_gReplFun (n : ℕ)
    (V : (((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1) → ℕ) :
    V ∘ gReplFun n =
      Sum.elim (fun i => V (Sum.inl (Sum.inl (Sum.inr i))))
        ![V (Sum.inl (Sum.inr 0)), V (Sum.inr 0)] := by
  funext x; rcases x with i | j
  · rfl
  · fin_cases j <;> rfl

@[simp] theorem comp_gReplFun2 (n : ℕ)
    (V : ((((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) → ℕ) :
    V ∘ gReplFun2 n =
      Sum.elim (fun i => V (Sum.inl (Sum.inl (Sum.inl (Sum.inr i)))))
        ![V (Sum.inl (Sum.inl (Sum.inr 0))), V (Sum.inr 0)] := by
  funext x; rcases x with i | j
  · rfl
  · fin_cases j <;> rfl

@[simp] theorem comp_gReplMain (n : ℕ)
    (V : (((((Empty ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) → ℕ) :
    V ∘ gReplMain n =
      Sum.elim (fun i => V (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr i))))))
        ![V (Sum.inr 0), V (Sum.inl (Sum.inr 0))] := by
  funext x; rcases x with i | j
  · rfl
  · fin_cases j <;> rfl

/-- **Replacement schema instance** for a first-order formula `φ` with `n`
    parameters, one input variable (`Fin 2` slot `0`) and one output variable
    (`Fin 2` slot `1`): if `φ` is functional, then the image of any set exists,
    `(∀ u, ∃! v, φ) → ∀ a, ∃ b, ∀ v, (v ∈ b ↔ ∃ u, u ∈ a ∧ φ)`. -/
noncomputable def replInstance (n : ℕ) (φ : LMem.Formula (Fin n ⊕ Fin 2)) :
    LMem.Sentence :=
  let funcHyp : LMem.Formula (Empty ⊕ Fin n) :=
    Formula.iAlls (Fin 1)
      (Formula.iExs (Fin 1)
        ((Formula.relabel (gReplFun n) φ) ⊓
         (Formula.iAlls (Fin 1)
           ((Formula.relabel (gReplFun2 n) φ).imp
            (eqF (Sum.inr 0) (Sum.inl (Sum.inr 0)))))))
  let mainPart : LMem.Formula (Empty ⊕ Fin n) :=
    Formula.iAlls (Fin 1)
      (Formula.iExs (Fin 1)
        (Formula.iAlls (Fin 1)
          ((memF (Sum.inr 0) (Sum.inl (Sum.inr 0))).iff
           (Formula.iExs (Fin 1)
             ((memF (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))) ⊓
              (Formula.relabel (gReplMain n) φ))))))
  Formula.iAlls (Fin n) (funcHyp.imp mainPart)

/-! ## The theory `RGFFinSetTheory = ZF − Infinity + ¬Infinity` -/

/-- The RGF first-order set theory: the finite (hereditarily-finite) set theory
    `ZF − Infinity + ¬Infinity`, with full first-order Separation and Replacement
    schemas. -/
def RGFFinSetTheory : LMem.Theory :=
  ({extAx, emptyAx, pairingAx, unionAx, powersetAx, foundationAx,
      Formula.not infinityAx} : Set (LMem.Sentence))
  ∪ (Set.range (fun p : Σ n, LMem.Formula (Fin n ⊕ Fin 1) => sepInstance p.1 p.2))
  ∪ (Set.range (fun p : Σ n, LMem.Formula (Fin n ⊕ Fin 2) => replInstance p.1 p.2))

/-! ## The Ackermann model satisfies every axiom -/

theorem ackModel_ext : ℕ ⊨ extAx := by
  unfold extAx; simp +decide [ FirstOrder.Language.Sentence.Realize ] ;
  exact fun i hi => RGF.RGFSet.ext fun x => hi ( fun _ => x )

theorem ackModel_empty : ℕ ⊨ emptyAx := by
  unfold emptyAx;
  simp +decide [ FirstOrder.Language.Sentence.Realize, Formula.realize_iExs, Formula.realize_iAlls, realize_memF ];
  exact ⟨ fun _ => 0, fun _ => RGF.RGFSet.empty _ ⟩

theorem ackModel_pairing : ℕ ⊨ pairingAx := by
  simp +decide [ Sentence.Realize, pairingAx, Formula.realize_iAlls, Formula.realize_iExs, Formula.realize_iff, Formula.realize_sup, realize_memF, realize_eqF ];
  intro i
  obtain ⟨z, hz⟩ := RGF.RGFSet.pairing (i 0) (i 1)
  use fun _ => z
  intro i_2
  simp [hz]

theorem ackModel_union : ℕ ⊨ unionAx := by
  simp +decide [ unionAx, FirstOrder.Language.Sentence.Realize ];
  intro i;
  use fun _ => RGF.RGFSet.union (i 0) |> Classical.choose;
  intro j; have := Classical.choose_spec ( RGF.RGFSet.union ( i 0 ) ) ; simp_all +decide ;
  exact ⟨ fun ⟨ y, hy₁, hy₂ ⟩ => ⟨ fun _ => y, hy₁, hy₂ ⟩, fun ⟨ y, hy₁, hy₂ ⟩ => ⟨ y 0, hy₁, hy₂ ⟩ ⟩

theorem ackModel_powerset : ℕ ⊨ powersetAx := by
  unfold powersetAx;
  simp +decide [ FirstOrder.Language.Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs, Formula.realize_iff ];
  intro i
  obtain ⟨z, hz⟩ := RGFSet.powerset (i 0);
  use fun _ => z;
  intro x; specialize hz ( x 0 ) ; simp_all +decide ;
  exact ⟨ fun h y hy => h _ hy, fun h d hd => h ( fun _ => d ) hd ⟩

theorem ackModel_foundation : ℕ ⊨ foundationAx := by
  simp +decide [ foundationAx, FirstOrder.Language.Sentence.Realize ];
  intro i x hx
  obtain ⟨y, hy⟩ : ∃ y, RGFSet.Mem y (i 0) ∧ ∀ z, RGFSet.Mem z y → ¬ RGFSet.Mem z (i 0) := by
    exact RGFSet.foundation ( i 0 ) ( by rintro h; simp_all +decide [ RGFSet.empty ] );
  exact ⟨ fun _ => y, hy.1, fun z hz => hy.2 _ hz ⟩

theorem ackModel_not_infinity : ℕ ⊨ Formula.not infinityAx := by
  have h_inf : ¬∃ z, Mem 0 z ∧ ∀ y, Mem y z → ∃ w, Mem w z ∧ ∀ c, Mem c w ↔ (c = y ∨ Mem c y) :=
    not_infinity
  contrapose! h_inf; simp_all +decide [ FirstOrder.Language.Sentence.Realize ] ;
  unfold infinityAx at h_inf;
  simp +decide [ Formula.realize_iExs, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf, Formula.realize_sup, Formula.realize_not, Formula.realize_iff, realize_memF, realize_eqF ] at h_inf;
  obtain ⟨ z, ⟨ e, he₁, he₂ ⟩, he₃ ⟩ := h_inf; use z 0; simp_all +decide [ Fin.eq_zero ] ;
  have h_e_zero : e 0 = 0 := by
    contrapose! he₂;
    have h_e_zero : ∃ i, i < e 0 ∧ Nat.testBit (e 0) i = true := by
      use Nat.log 2 (e 0);
      refine' ⟨ Nat.log_lt_of_lt_pow ( by positivity ) ( Nat.recOn ( e 0 ) ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ ] at * ; linarith ), _ ⟩;
      rw [ Nat.testBit ];
      norm_num [ Nat.shiftRight_eq_div_pow ];
      rw [ Nat.mod_eq_of_lt ];
      · exact Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by rw [ mul_comm, ← Nat.pow_succ' ] ; exact Nat.lt_pow_succ_log_self ( by decide ) _ ) ( Nat.div_pos ( Nat.pow_le_of_le_log ( by positivity ) ( by linarith ) ) ( by positivity ) );
      · exact Nat.div_lt_of_lt_mul <| by rw [ mul_comm, ← Nat.pow_succ' ] ; exact Nat.lt_pow_succ_log_self ( by decide ) _;
    exact ⟨ fun _ => h_e_zero.choose, h_e_zero.choose_spec.2 ⟩;
  simp_all +decide ;
  exact fun y hy => by obtain ⟨ w, hw₁, hw₂ ⟩ := he₃ ( fun _ => y ) hy; exact ⟨ w 0, hw₁, fun c => by simpa using hw₂ ( fun _ => c ) ⟩ ;

theorem ackModel_sep (n : ℕ) (φ : LMem.Formula (Fin n ⊕ Fin 1)) :
    ℕ ⊨ sepInstance n φ := by
  unfold sepInstance; simp +decide [ FirstOrder.Language.Sentence.Realize ] ;
  intro p a; have := @RGF.RGFSet.separation;
  convert this ( a 0 ) ( fun c => φ.Realize ( Sum.elim ( fun i => p i ) ( fun _ => c ) ) ) using 1;
  · constructor;
    · rintro ⟨ z, hz ⟩;
      convert this ( a 0 ) ( fun c => φ.Realize ( Sum.elim p ( fun _ => c ) ) ) using 1;
      exact Classical.decPred _;
    · rintro ⟨ z, hz ⟩ ; use fun _ => z; intro i; convert hz ( i 0 ) using 1;
      congr! 2;
      ext ( _ | _ ) <;> rfl;
  · exact fun _ => Classical.propDecidable _

/-- The model relation defined by a replacement formula `φ` together with a
    parameter assignment `p`: `ReplRel φ p u v` holds iff `φ` is realized with the
    parameters `p`, the input slot equal to `u`, and the output slot equal to `v`. -/
def ReplRel (n : ℕ) (φ : LMem.Formula (Fin n ⊕ Fin 2)) (p : Fin n → ℕ) (u v : ℕ) :
    Prop :=
  φ.Realize (Sum.elim p ![u, v])

/-- **Realization of a replacement instance**, reduced to plain first-order content
    over `ℕ` (the De Bruijn / relabelling bookkeeping discharged). -/
theorem realize_replInstance (n : ℕ) (φ : LMem.Formula (Fin n ⊕ Fin 2)) :
    (ℕ ⊨ replInstance n φ) ↔
      ∀ p : Fin n → ℕ,
        (∀ u : ℕ, ∃ v : ℕ, ReplRel n φ p u v ∧ ∀ w : ℕ, ReplRel n φ p u w → w = v) →
        ∀ a : ℕ, ∃ b : ℕ, ∀ c : ℕ, Mem c b ↔ ∃ u : ℕ, Mem u a ∧ ReplRel n φ p u c := by
  unfold replInstance ReplRel
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_imp, Formula.realize_inf, Formula.realize_iff,
    Formula.realize_relabel, realize_memF, realize_eqF,
    comp_gReplFun, comp_gReplFun2, comp_gReplMain, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h p hp a
    obtain ⟨b, hb⟩ := h p (fun w => by
      obtain ⟨v, hv1, hv2⟩ := hp (w 0)
      exact ⟨fun _ => v, by simpa using hv1,
        fun w' hw' => by simpa using hv2 (w' 0) (by simpa using hw')⟩) (fun _ => a)
    refine ⟨b 0, fun c => ?_⟩
    have := hb (fun _ => c)
    rw [this]
    constructor
    · rintro ⟨u, hu1, hu2⟩; exact ⟨u 0, by simpa using hu1, by simpa using hu2⟩
    · rintro ⟨u, hu1, hu2⟩; exact ⟨fun _ => u, by simpa using hu1, by simpa using hu2⟩
  · intro h p hp a
    obtain ⟨b, hb⟩ := h p (fun u => by
      obtain ⟨v, hv1, hv2⟩ := hp (fun _ => u)
      exact ⟨v 0, by simpa using hv1,
        fun w hw => by simpa using hv2 (fun _ => w) (by simpa using hw)⟩) (a 0)
    refine ⟨fun _ => b, fun c => ?_⟩
    have := hb (c 0)
    rw [this]
    constructor
    · rintro ⟨u, hu1, hu2⟩; exact ⟨fun _ => u, by simpa using hu1, by simpa using hu2⟩
    · rintro ⟨u, hu1, hu2⟩; exact ⟨u 0, by simpa using hu1, by simpa using hu2⟩

theorem ackModel_repl (n : ℕ) (φ : LMem.Formula (Fin n ⊕ Fin 2)) :
    ℕ ⊨ replInstance n φ := by
  rw [realize_replInstance]
  intro p hfunc a
  classical
  -- extract the function determined by the functional hypothesis
  choose f hf huniq using hfunc
  obtain ⟨z, hz⟩ := RGF.RGFSet.replacement a f
  refine ⟨z, fun c => ?_⟩
  rw [hz]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, hf y⟩
  · rintro ⟨u, hu, hφ⟩
    exact ⟨u, hu, huniq u c hφ⟩

/-- **The Ackermann structure is a model of `RGFFinSetTheory`.** -/
instance ackModel_models : ℕ ⊨ RGFFinSetTheory := by
  constructor
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · -- finite axioms
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ackModel_ext
    · exact ackModel_empty
    · exact ackModel_pairing
    · exact ackModel_union
    · exact ackModel_powerset
    · exact ackModel_foundation
    · exact ackModel_not_infinity
  · -- separation schema
    obtain ⟨⟨n, ψ⟩, rfl⟩ := hφ
    exact ackModel_sep n ψ
  · -- replacement schema
    obtain ⟨⟨n, ψ⟩, rfl⟩ := hφ
    exact ackModel_repl n ψ

/-! ## Relative consistency: `Con(ZFC) → Con(RGF)` -/

/-- **Relative consistency.**  `RGFFinSetTheory` is satisfiable: it has the model
    `(ℕ, ∈ₐ)`, which is constructed entirely inside Lean's type theory
    (interpretable in ZFC + universes).  This is exactly the reduction
    `Con(ZFC) → Con(RGF)`. -/
theorem consistency : RGFFinSetTheory.IsSatisfiable :=
  Theory.Model.isSatisfiable ℕ

/-- **Syntactic form of consistency**: the theory does not prove `⊥`. -/
theorem not_models_falsum : ¬ RGFFinSetTheory ⊨ᵇ (⊥ : LMem.Sentence) := by
  intro hbot
  obtain ⟨M⟩ := consistency
  have := Theory.models_sentence_iff.1 hbot M
  simpa using this

/-! ## Consistency strength: the double Ackermann interpretation -/

/-- The Ackermann coding is a **bijection** `ℕ ≃ Finset ℕ`: a code `n` corresponds
    to its finite set of elements, and conversely.  This is the recursive
    interpretation of finite set theory inside arithmetic. -/
def ackCodeEquiv : ℕ ≃ Finset ℕ where
  toFun := elems
  invFun := code
  left_inv := code_elems
  right_inv := elems_code

/-- The Ackermann membership relation is exactly "being an element of the coded
    finite set". -/
theorem ack_mem_iff (a b : ℕ) : Mem a b ↔ a ∈ ackCodeEquiv b :=
  (mem_elems b a).symm

/-- The Ackermann coding is also a **bijection** onto the genuine hereditarily
    finite `ZFSet`s: codes ↔ `{x : ZFSet // IsHF x}`. -/
noncomputable def hfCodeEquiv : ℕ ≃ {x : ZFSet // IsHF x} :=
  Equiv.ofBijective (fun n => ⟨toZF n, isHF_toZF n⟩)
    ⟨fun a b h => toZF_inj (Subtype.ext_iff.1 h),
     fun y => by
       obtain ⟨n, hn⟩ := exists_code_of_isHF y.1 y.2
       exact ⟨n, Subtype.ext hn⟩⟩

/-- Under the hereditarily-finite `ZFSet` interpretation, the Ackermann membership
    relation is exactly genuine `∈` in the ZF universe. -/
theorem hfCodeEquiv_mem (a b : ℕ) :
    ((hfCodeEquiv a : {x : ZFSet // IsHF x}) : ZFSet) ∈
      ((hfCodeEquiv b : {x : ZFSet // IsHF x}) : ZFSet) ↔ Mem a b :=
  toZF_mem_toZF a b

/-!
## Summary: the exact consistency-strength location of RGF

The first-order theory `RGFFinSetTheory` is `ZF − Infinity + ¬Infinity`, i.e.
**finite set theory** — the theory of the hereditarily-finite universe `HF`.

* **Relative consistency.**  `consistency` and `not_models_falsum` give
  `Con(ZFC) → Con(RGF)`: a model of the theory is built inside Lean's type theory,
  which is interpretable in `ZFC + universes`.

* **Exact strength.**  `ZF − Infinity` (equivalently `RGFFinSetTheory` together with
  classical logic) is mutually interpretable with Peano Arithmetic `PA`; the two
  Ackermann interpretations `ackCodeEquiv : ℕ ≃ Finset ℕ` and
  `hfCodeEquiv : ℕ ≃ {x : ZFSet // IsHF x}` (with `ack_mem_iff`, `hfCodeEquiv_mem`)
  exhibit the membership structure recursively inside arithmetic and identify it
  with the genuine hereditarily-finite sets.  Hence RGF's set-theoretic core sits at
  the very bottom of the consistency hierarchy: at the *finitist* level of `PA`,
  strictly weaker than full `ZFC` (which proves `Con(PA)`, hence `Con(RGF)`), and far
  below any large-cardinal assumption — RGF assumes no infinite set, so it lives
  beneath the first rung (inaccessible cardinals) of the large-cardinal ladder.
-/

end RGFConsistencyStrength
end RGF