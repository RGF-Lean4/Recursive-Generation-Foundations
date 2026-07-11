/-
  RGF2/Hierarchy/HereditarilyFinite.lean   (module `RGF2.Hierarchy.HereditarilyFinite`)
  — layer 1: the `V_ω` stage and the precise interface with the RGF 1.0 HF core.

  **RGF 2.0 — the exact docking of the cumulative hierarchy with RGF 1.0.**

  RGF 1.0 codes sets as *finite* Ackermann integers `(ℕ, ∈ₐ)`; that model is the
  hereditarily finite universe `HF = ZF − Infinity` (`RGFSetTheory.lean`,
  `RGFZFBenchmark.lean`, `RGFConsistencyStrength.lean`).  There the Ackermann codes
  are already shown to biject, membership-preservingly, with the genuine
  hereditarily finite `ZFSet`s:

      RGF.RGFSet.toZF        : ℕ → ZFSet             (`toZF_mem_toZF`)
      RGF.RGFSet.IsHF        : ZFSet → Prop          (textbook HF predicate)
      RGFConsistencyStrength.hfCodeEquiv : ℕ ≃ {x : ZFSet // IsHF x}   (`hfCodeEquiv_mem`)

  This file connects that HF core to the RGF 2.0 cumulative hierarchy by proving
  that the ω-th stage `V_ω` is *exactly* the hereditarily finite universe:

    * `isHF_iff_rank_lt_omega`   `IsHF x ↔ x.rank < ω`;
    * `mem_Vomega_iff_isHF`      `x ∈ V_ω ↔ IsHF x`;
    * `mem_Vomega₂_iff`          the same for the RGF 2.0 set universe `RGFSet₂`;
    * `Vomega₂_equiv_ackCodes`   a **membership-preserving bijection**
                                 `ℕ ≃ {x : RGFSet₂ // x ∈ V_ω}` between the RGF 1.0
                                 Ackermann codes and the members of `V_ω`
                                 (`Vomega₂_equiv_mem`);
    * `Vomega_is_RGF1_core`      the capstone: `V_ω` is exactly the RGF 1.0 HF core,
                                 sitting inside the larger RGF 2.0 universe, and the
                                 upgrade is *strict* — `ω` itself is a genuinely new
                                 object living above `V_ω`.

  This makes precise the sense in which RGF 2.0 is a strict upgrade of RGF 1.0:
  everything RGF 1.0 could ever express is precisely the bottom stage `V_ω` of the
  RGF 2.0 hierarchy, and the whole transfinite tower `V_α`, `α ≥ ω`, is new.
-/
import Mathlib
import RGF.Math.SetTheory.RGF2.Core.WType
import RGF.Math.SetTheory.RGF2.Hierarchy.Cumulative
import RGF.Math.SetTheory.RGFZFBenchmark
import RGF.Math.SetTheory.RGFConsistencyStrength

open ZFSet Ordinal

namespace RGF
namespace RGF2

/-! ## `V_ n` at a finite stage is hereditarily finite -/

/-- Each finite von Neumann stage `V_ n` is a hereditarily finite set. -/
theorem isHF_vonNeumann_nat (n : ℕ) : RGF.RGFSet.IsHF (V_ (n : Ordinal.{0})) := by
  induction n with
  | zero => rw [Nat.cast_zero, ZFSet.vonNeumann_zero]; exact RGF.RGFSet.hf_empty
  | succ k ih =>
      have hc : ((k + 1 : ℕ) : Ordinal) = Order.succ (k : Ordinal) := by
        rw [Nat.cast_succ, Ordinal.add_one_eq_succ]
      rw [hc, ZFSet.vonNeumann_succ]
      exact RGF.RGFSet.hf_powerset ih

/-- **Forward:** a set of finite rank is hereditarily finite. -/
theorem isHF_of_rank_lt_omega {x : ZFSet.{0}} (hx : x.rank < Ordinal.omega0) :
    RGF.RGFSet.IsHF x := by
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 hx
  have hxmem : x ∈ V_ (Order.succ x.rank) := by
    rw [ZFSet.mem_vonNeumann]; exact Order.lt_succ _
  have hsucc : Order.succ x.rank = ((k + 1 : ℕ) : Ordinal) := by
    rw [hk, Nat.cast_succ, Ordinal.add_one_eq_succ]
  rw [hsucc] at hxmem
  exact (isHF_vonNeumann_nat (k + 1)).mem hxmem

/-
**Reverse:** a hereditarily finite set has finite rank.
-/
theorem rank_lt_omega_of_isHF {x : ZFSet.{0}} (hx : RGF.RGFSet.IsHF x) :
    x.rank < Ordinal.omega0 := by
  induction' x using ZFSet.inductionOn with x ih;
  obtain ⟨ hx₁, hx₂ ⟩ := RGF.RGFSet.isHF_iff.1 hx;
  obtain ⟨ N, hN ⟩ := hx₁.exists_finset_coe;
  -- Since $N$ is finite, we can take $N$ as the maximum of the ranks of its elements.
  obtain ⟨ M, hM ⟩ : ∃ M : ℕ, ∀ y ∈ N, y.rank ≤ M := by
    have hM : ∀ y ∈ N, y.rank < Ordinal.omega0 := by
      exact fun y hy => ih y ( hN.subset hy ) ( hx₂ y ( hN.subset hy ) );
    choose! M hM using fun y hy => Ordinal.lt_omega0.mp ( hM y hy );
    exact ⟨ Finset.sup N M, fun y hy => hM y hy ▸ Nat.cast_le.mpr ( Finset.le_sup ( f := M ) hy ) ⟩;
  refine' lt_of_le_of_lt ( ZFSet.rank_le_iff.mpr _ ) ( Ordinal.nat_lt_omega0 ( M + 1 ) );
  exact fun y hy => lt_of_le_of_lt ( hM y <| hN.symm.subset hy ) ( Nat.cast_lt.mpr <| Nat.lt_succ_self _ )

/-- **`V_ω` = HF (rank form).** `IsHF x ↔ x.rank < ω`. -/
theorem isHF_iff_rank_lt_omega {x : ZFSet.{0}} :
    RGF.RGFSet.IsHF x ↔ x.rank < Ordinal.omega0 :=
  ⟨rank_lt_omega_of_isHF, isHF_of_rank_lt_omega⟩

/-- **`V_ω` = HF (stage form).** The ω-th von Neumann stage consists of exactly the
hereditarily finite sets. -/
theorem mem_Vomega_iff_isHF (x : ZFSet.{0}) :
    x ∈ V_ Ordinal.omega0 ↔ RGF.RGFSet.IsHF x := by
  rw [ZFSet.mem_vonNeumann, ← isHF_iff_rank_lt_omega]

/-! ## The `V_ω` stage of the RGF 2.0 universe -/

/-- The ω-th stage of the RGF 2.0 cumulative hierarchy. -/
noncomputable def Vomega₂ : RGFSet₂.{0} := Vhier Ordinal.omega0

/-- A RGF 2.0 set lies in `V_ω` iff it is (under the canonical `RGFSet₂ ≃ ZFSet`)
hereditarily finite. -/
theorem mem_Vomega₂_iff (x : RGFSet₂.{0}) :
    Mem₂ x Vomega₂ ↔ RGF.RGFSet.IsHF (equivZF x) := by
  rw [Vomega₂, mem_Vhier_iff, rank₂, ← isHF_iff_rank_lt_omega]

/-! ## The precise docking with the RGF 1.0 Ackermann core -/

/-- The subtype of `V_ω`-members of the RGF 2.0 universe is equivalent to the genuine
hereditarily finite `ZFSet`s, via the canonical `RGFSet₂ ≃ ZFSet`. -/
noncomputable def Vomega₂SubtypeEquiv :
    {x : RGFSet₂.{0} // Mem₂ x Vomega₂} ≃ {y : ZFSet.{0} // RGF.RGFSet.IsHF y} :=
  Equiv.subtypeEquiv equivZF (fun x => mem_Vomega₂_iff x)

/-- **The membership-preserving bijection** between the RGF 1.0 Ackermann codes `ℕ`
and the members of `V_ω` in the RGF 2.0 universe. -/
noncomputable def Vomega₂_equiv_ackCodes :
    ℕ ≃ {x : RGFSet₂.{0} // Mem₂ x Vomega₂} :=
  RGF.RGFConsistencyStrength.hfCodeEquiv.trans Vomega₂SubtypeEquiv.symm

/-- Under the docking bijection, RGF 2.0 membership inside `V_ω` coincides *exactly*
with RGF 1.0 Ackermann membership `∈ₐ`. -/
theorem Vomega₂_equiv_mem (a b : ℕ) :
    Mem₂ (Vomega₂_equiv_ackCodes a : RGFSet₂.{0}) (Vomega₂_equiv_ackCodes b : RGFSet₂.{0})
      ↔ RGF.RGFSet.Mem a b := by
  have key : ∀ n : ℕ, equivZF (Vomega₂_equiv_ackCodes n : RGFSet₂.{0})
      = ((RGF.RGFConsistencyStrength.hfCodeEquiv n :
          {x : ZFSet.{0} // RGF.RGFSet.IsHF x}) : ZFSet.{0}) := by
    intro n
    simp only [Vomega₂_equiv_ackCodes, Vomega₂SubtypeEquiv, Equiv.trans_apply,
      Equiv.subtypeEquiv_symm, Equiv.subtypeEquiv_apply, Equiv.apply_symm_apply]
  rw [Mem₂, key a, key b]
  exact RGF.RGFConsistencyStrength.hfCodeEquiv_mem a b

/-! ## The strict upgrade: `ω` is a genuinely new object -/

/-- The set `ω` is not hereditarily finite. -/
theorem omega_not_isHF : ¬ RGF.RGFSet.IsHF (ZFSet.omega : ZFSet.{0}) := by
  intro h
  exact RGF.RGFSet.no_inductiveSet_HF
    ⟨ZFSet.omega, h, ZFSet.omega_zero, fun _ hy => ZFSet.omega_succ hy⟩

/-- `ω` does not appear in `V_ω`. -/
theorem omega_notin_Vomega : (ZFSet.omega : ZFSet.{0}) ∉ V_ Ordinal.omega0 := by
  rw [mem_Vomega_iff_isHF]; exact omega_not_isHF

/-- `ω` is a genuinely new object: it is absent from `V_ω` yet appears at some higher
stage of the hierarchy. -/
theorem omega_new_object :
    (ZFSet.omega : ZFSet.{0}) ∉ V_ Ordinal.omega0 ∧ ∃ o, (ZFSet.omega : ZFSet.{0}) ∈ V_ o :=
  ⟨omega_notin_Vomega, ZFSet.exists_mem_vonNeumann ZFSet.omega⟩

/-- **Capstone.** `V_ω` is *exactly* the RGF 1.0 hereditarily-finite core, and the
RGF 2.0 upgrade over it is strict.  Concretely:

1. `V_ω` consists exactly of the hereditarily finite sets;
2. there is a membership-preserving bijection between the RGF 1.0 Ackermann codes
   `ℕ` and the members of `V_ω`;
3. `ω` itself is a genuinely new object — absent from `V_ω`, present higher up. -/
theorem Vomega_is_RGF1_core :
    (∀ x : RGFSet₂.{0}, Mem₂ x Vomega₂ ↔ RGF.RGFSet.IsHF (equivZF x)) ∧
    (∀ a b : ℕ,
      Mem₂ (Vomega₂_equiv_ackCodes a : RGFSet₂.{0}) (Vomega₂_equiv_ackCodes b : RGFSet₂.{0})
        ↔ RGF.RGFSet.Mem a b) ∧
    ((ZFSet.omega : ZFSet.{0}) ∉ V_ Ordinal.omega0 ∧ ∃ o, (ZFSet.omega : ZFSet.{0}) ∈ V_ o) :=
  ⟨mem_Vomega₂_iff, Vomega₂_equiv_mem, omega_new_object⟩

end RGF2
end RGF