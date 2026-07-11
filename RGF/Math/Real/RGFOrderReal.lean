/-
  Foundations/RGFOrderReal.lean

  Order structure on the RGF reals and the ordered ring isomorphism with ℝ.

  We equip `RGFReal'` with the standard Cauchy-sequence order: `a ≤ b` holds iff
  for every error level `n`, the approximations eventually satisfy
  `a.approx k ≤ b.approx k + 1/(n+1)` (pointwise comparison up to a vanishing
  rational error).  This order is shown to be well defined on equivalence classes
  and to correspond exactly to the order of the standard reals through the
  canonical map `toReal`.  Packaging this with the ring isomorphism
  `ringEquivReal` yields the *ordered* ring isomorphism `RGFReal' ≃+*o ℝ`.
-/
import Mathlib
import RGF.Math.Real.RGFField

namespace RGF

open RGFNat RGFInt RGFRat

/-- Native pointwise order on pre-reals: `a ≤ b` iff for every error level `n`,
    eventually `a.approx k ≤ b.approx k + 1/(n+1)` (in `RGFRat`). -/
def PreReal.le (a b : PreReal) : Prop :=
  ∀ n : RGFNat, ∃ N : RGFNat, ∀ k : RGFNat, N ≤ k →
    a.approx k ≤ b.approx k + RGFRat.oneDivSucc n

/-- The order condition, transferred to an inequality in `ℚ` through `toRat`. -/
theorem PreReal.le_iff_rat (a b : PreReal) :
    PreReal.le a b ↔ ∀ n : RGFNat, ∃ N : RGFNat, ∀ k : RGFNat, N ≤ k →
      RGFRat.toRat (a.approx k) ≤ RGFRat.toRat (b.approx k) + 1 / ((n.toNat : ℚ) + 1) := by
  unfold PreReal.le
  constructor <;> intro h n <;> obtain ⟨N, hN⟩ := h n <;> exact ⟨N, fun k hk => by
    have := hN k hk
    rw [RGFRat.le_def, RGFRat.toRat_add, RGFRat.toRat_oneDivSucc] at *
    linarith [this]⟩

/-
The native order is well defined on equivalence classes.
-/
theorem PreReal.le_well_defined {a₁ a₂ b₁ b₂ : PreReal}
    (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) : PreReal.le a₁ b₁ ↔ PreReal.le a₂ b₂ := by
  constructor <;> intro h <;> simp_all +decide only [le_iff_rat];
  · intro n
    obtain ⟨m, hm⟩ : ∃ m : RGFNat, 1 / (m.toNat + 1 : ℚ) ≤ (1 / (n.toNat + 1 : ℚ)) / 3 := by
      use RGFNat.ofNat' ( 3 * ( n.toNat + 1 ) );
      rw [ div_div, div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ ofNat' ];
      grind +suggestions
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : RGFNat, ∀ k : RGFNat, N₁ ≤ k → |RGFRat.toRat (a₁.approx k) - RGFRat.toRat (a₂.approx k)| ≤ 1 / (m.toNat + 1 : ℚ) := by
      convert ha m using 1;
      ext; simp [RGFRat.isSmall_iff, RGFRat.toRat_sub]
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : RGFNat, ∀ k : RGFNat, N₂ ≤ k → |RGFRat.toRat (b₁.approx k) - RGFRat.toRat (b₂.approx k)| ≤ 1 / (m.toNat + 1 : ℚ) := by
      convert hb m using 1;
      ext; simp +decide [ isSmall_iff, RGFRat.toRat_sub ] ;
    obtain ⟨N₃, hN₃⟩ : ∃ N₃ : RGFNat, ∀ k : RGFNat, N₃ ≤ k → RGFRat.toRat (a₁.approx k) ≤ RGFRat.toRat (b₁.approx k) + 1 / (m.toNat + 1 : ℚ) := by
      exact h m;
    use RGFNat.max N₁ (RGFNat.max N₂ N₃);
    intro k hk; linarith [ abs_le.mp ( hN₁ k ( RGFNat.le_max_left _ _ |> le_trans <| hk ) ), abs_le.mp ( hN₂ k ( RGFNat.le_max_right _ _ |> le_trans ( RGFNat.le_max_left _ _ ) |> le_trans <| hk ) ), hN₃ k ( RGFNat.le_max_right _ _ |> le_trans ( RGFNat.le_max_right _ _ ) |> le_trans <| hk ) ] ;
  · intro n
    obtain ⟨m, hm⟩ : ∃ m : RGFNat, (1 / ((m.toNat : ℚ) + 1)) ≤ (1 / ((n.toNat : ℚ) + 1)) / 3 := by
      use RGFNat.ofNat' (3 * (n.toNat + 1));
      rw [ div_div, div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ ofNat' ];
      grind +suggestions;
    obtain ⟨N₁, hN₁⟩ := ha m
    obtain ⟨N₂, hN₂⟩ := hb m
    obtain ⟨N₃, hN₃⟩ := h m;
    use RGFNat.max N₁ (RGFNat.max N₂ N₃);
    intro k hk; have := hN₁ k ( le_trans ( RGFNat.le_max_left _ _ ) hk ) ; have := hN₂ k ( le_trans ( RGFNat.le_max_right _ _ |> le_trans ( RGFNat.le_max_left _ _ ) ) hk ) ; have := hN₃ k ( le_trans ( RGFNat.le_max_right _ _ |> le_trans ( RGFNat.le_max_right _ _ ) ) hk ) ; simp_all +decide [ RGFRat.isSmall_iff, RGFRat.toRat_sub ] ;
    linarith [ abs_le.mp ‹|(a₁.approx k).toRat - (a₂.approx k).toRat| ≤ (m.toNat + 1 : ℚ)⁻¹›, abs_le.mp ‹|(b₁.approx k).toRat - (b₂.approx k).toRat| ≤ (m.toNat + 1 : ℚ)⁻¹› ]

namespace RGFReal'

/-- The order relation on `RGFReal'`, induced by the native pointwise order. -/
def leRel : RGFReal' → RGFReal' → Prop :=
  Quotient.lift₂ PreReal.le
    (fun _ _ _ _ ha hb => propext (PreReal.le_well_defined ha hb))

/-- Order on `RGFReal'`, induced by the native pointwise order on pre-reals. -/
instance : LE RGFReal' := ⟨leRel⟩

theorem le_iff_leRel (a b : RGFReal') : a ≤ b ↔ leRel a b := Iff.rfl

theorem le_mk (a b : PreReal) :
    leRel (Quotient.mk PreReal.preRealSetoid a) (Quotient.mk PreReal.preRealSetoid b)
      ↔ PreReal.le a b := Iff.rfl

/-
**Order isomorphism, pointwise direction.** The canonical map `toReal`
    preserves and reflects the order.
-/
theorem toReal_le_iff {a b : RGFReal'} : toReal a ≤ toReal b ↔ a ≤ b := by
  constructor;
  · obtain ⟨ x, rfl ⟩ := Quotient.exists_rep a; obtain ⟨ y, rfl ⟩ := Quotient.exists_rep b; simp +decide [ RGFReal'.toReal_mk ] ;
    intro h_le
    apply RGFReal'.le_mk x y |>.2
    intro n
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j ≥ N, (cauSeqOf x j : ℚ) ≤ (cauSeqOf y j : ℚ) + 1 / ((n.toNat : ℚ) + 1) := by
      cases' h_le with h_lt h_eq;
      · obtain ⟨ K, hK ⟩ := h_lt;
        obtain ⟨ i, hi ⟩ := hK.2; use i; intro j hj; have := hi j hj; norm_num at *; linarith [ inv_pos.mpr ( by positivity : 0 < ( n.toNat : ℚ ) + 1 ) ] ;
      · have := h_eq ( 1 / ( n.toNat + 1 ) ) ( by positivity );
        obtain ⟨ N, hN ⟩ := this; use N; intro j hj; specialize hN j hj; rw [ abs_lt ] at hN; linarith! [ CauSeq.sub_apply ( cauSeqOf x ) ( cauSeqOf y ) j ] ;
    use RGFNat.ofNat' N;
    intro k hk; specialize hN k.toNat ( by
      grind +suggestions ) ; simp_all +decide [ cauSeqOf_apply ] ;
    grind +suggestions;
  · contrapose!;
    obtain ⟨ x, rfl ⟩ := Quotient.exists_rep a; obtain ⟨ y, rfl ⟩ := Quotient.exists_rep b; simp +decide [ RGFReal'.le_iff_leRel, RGFReal'.le_mk, RGF.PreReal.le_iff_rat ] ;
    intro h
    obtain ⟨K, hK_pos, i, hi⟩ : ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ (cauSeqOf x - cauSeqOf y) j := by
      convert h using 1;
    obtain ⟨ m, hm ⟩ := RGFRat.exists_index ( K / 2 ) ( half_pos hK_pos );
    refine' ⟨ m, fun n => _ ⟩;
    refine' ⟨ RGFNat.ofNat' ( Max.max i n.toNat ), _, _ ⟩ <;> norm_num at *;
    · grind +suggestions;
    · linarith [ hi ( Max.max i n.toNat ) ( le_max_left _ _ ) ]

/-- **The ordered ring isomorphism `RGFReal' ≃+*o ℝ`.** The RGF reals agree with
    the standard reals on the additive, multiplicative *and* order structure. -/
noncomputable def orderedRingEquivReal : RGFReal' ≃+*o ℝ :=
  { ringEquivReal with map_le_map_iff' := fun {_ _} => toReal_le_iff }

@[simp] theorem orderedRingEquivReal_apply (a : RGFReal') :
    orderedRingEquivReal a = toReal a := rfl

end RGFReal'
end RGF