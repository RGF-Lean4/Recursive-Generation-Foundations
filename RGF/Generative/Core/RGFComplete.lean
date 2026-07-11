/-
  Foundations/RGFComplete.lean

  Completeness of the RGF reals.

  We construct the canonical map `RGFReal'.toReal : RGFReal' → ℝ` sending an
  `RGFNat`-indexed Cauchy sequence of `RGFRat` to the limit of the corresponding
  standard `ℚ`-Cauchy sequence (`Real.mk`). We show:

  * `toReal` is a ring homomorphism (preserves `0, 1, +, -, *`);
  * `toReal` is bijective.

  Consequently `RGFReal'` is, as a ring, isomorphic to `ℝ` (`RGFReal'.equivReal`),
  which is the precise sense in which `RGFReal'` is *the* complete ordered field.
  The explicit completeness statement (every Cauchy sequence converges) is proved
  in `Foundations.RGFField`.
-/
import Mathlib
import RGF.Math.Real.RGFReal

namespace RGF

open RGFNat RGFInt

namespace RGFReal'

/-- The standard `ℚ`-valued sequence underlying a `PreReal`, re-indexed by `ℕ`. -/
def seqRat (x : PreReal) : ℕ → ℚ := fun k => RGFRat.toRat (x.approx (RGFNat.ofNat' k))

theorem isCauSeq_seqRat (x : PreReal) : IsCauSeq abs (seqRat x) := by
  intros ε hε_pos;
  -- By definition of `seqRat`, we know that `seqRat x j = RGFRat.toRat (x.approx (RGFNat.ofNat' j))`.
  set i₀ := RGF.RGFRat.exists_index (ε / 2) (half_pos hε_pos) with hi₀;
  obtain ⟨ n, hn ⟩ := i₀
  obtain ⟨ N, hN ⟩ := x.cauchy n
  use N.toNat
  intro j hj
  have hN_j : N ≤ RGFNat.ofNat' j := by
    grind +suggestions
  have hN_i : N ≤ RGFNat.ofNat' N.toNat := by
    grind +suggestions
  have h_diff : |RGFRat.toRat (x.approx (RGFNat.ofNat' j) - x.approx (RGFNat.ofNat' N.toNat))| ≤ 1 / ((n.toNat : ℚ) + 1) := by
    exact hN _ _ hN_j hN_i |> fun h => by simpa using RGFRat.isSmall_iff _ _ |>.1 h;
  have h_final : |seqRat x j - seqRat x N.toNat| ≤ 1 / ((n.toNat : ℚ) + 1) := by
    convert h_diff using 1;
    unfold seqRat; rw [ RGFRat.toRat_sub ] ;
  have h_final' : |seqRat x j - seqRat x N.toNat| < ε := by
    linarith
  exact h_final'

/-- The standard `ℚ`-Cauchy sequence underlying a `PreReal`. -/
def cauSeqOf (x : PreReal) : CauSeq ℚ abs := ⟨seqRat x, isCauSeq_seqRat x⟩

@[simp] theorem cauSeqOf_apply (x : PreReal) (k : ℕ) :
    (cauSeqOf x) k = RGFRat.toRat (x.approx (RGFNat.ofNat' k)) := rfl

theorem cauSeq_equiv_of_equiv {x y : PreReal} (h : PreReal.Equiv x y) :
    cauSeqOf x ≈ cauSeqOf y := by
  intro ε hε;
  obtain ⟨ n, hn ⟩ := RGFRat.exists_index ( ε / 2 ) ( half_pos hε );
  obtain ⟨ N, hN ⟩ := h n;
  use N.toNat;
  intro j hj; specialize hN ( RGFNat.ofNat' j ) ( by
    grind +suggestions ) ; simp_all +decide [ RGFRat.isSmall_iff ] ;
  convert lt_of_le_of_lt hN ( lt_of_le_of_lt hn ( half_lt_self hε ) ) using 1;
  rw [ RGFRat.toRat_sub ]

/-- The canonical map from RGF reals to the standard reals. -/
noncomputable def toReal : RGFReal' → ℝ :=
  Quotient.lift (fun x => Real.mk (cauSeqOf x))
    (fun _ _ h => Real.mk_eq.mpr (cauSeq_equiv_of_equiv h))

@[simp] theorem toReal_mk (x : PreReal) : toReal (Quotient.mk _ x) = Real.mk (cauSeqOf x) := rfl

theorem toReal_zero : toReal 0 = 0 := by
  convert Real.mk_zero;
  convert toReal_mk _;
  ext; simp [cauSeqOf];
  exact Eq.symm ( by exact RGF.RGFRat.toRat_zero )

theorem toReal_one : toReal 1 = 1 := by
  convert Real.mk_one using 1;
  convert toReal_mk _;
  ext; simp [RGF.RGFRat.one];
  convert RGF.RGFRat.toRat_one.symm

theorem toReal_add (a b : RGFReal') : toReal (a + b) = toReal a + toReal b := by
  induction a using Quotient.ind with | _ x => ?_
  induction b using Quotient.ind with | _ y => ?_
  show toReal (RGFReal'.add _ _) = _
  erw [RGFReal'.add, Quotient.lift₂_mk, toReal_mk, toReal_mk, toReal_mk, ← Real.mk_add]
  congr 1
  exact CauSeq.ext fun n => by simp +decide [cauSeqOf_apply, RGFRat.toRat_add]

theorem toReal_neg (a : RGFReal') : toReal (neg a) = - toReal a := by
  convert Real.mk_neg;
  rotate_right;
  exact cauSeqOf ( Quotient.out a );
  · rw [ ← Quotient.out_eq a ];
    convert toReal_mk _;
    ext; simp [cauSeqOf];
    unfold seqRat; simp +decide [ RGFRat.toRat_neg ] ;
  · convert toReal_mk ( Quotient.out a );
    exact Eq.symm ( Quotient.out_eq' a )

theorem toReal_mul (a b : RGFReal') : toReal (a * b) = toReal a * toReal b := by
  induction a using Quotient.ind;
  induction b using Quotient.ind ; simp_all +decide;
  convert Real.mk_mul;
  convert toReal_mk _;
  exact CauSeq.ext fun n => by simp +decide [ cauSeqOf_apply, RGFRat.toRat_mul ] ;

theorem toReal_sub (a b : RGFReal') : toReal (a - b) = toReal a - toReal b := by
  show toReal (a + neg b) = _
  rw [toReal_add, toReal_neg]; ring

theorem toReal_injective : Function.Injective toReal := by
  intro a b hab;
  induction a using Quotient.ind ; induction b using Quotient.ind ; simp_all +decide [ Real.mk_eq ];
  exact Quotient.sound <| by
    intro n
    obtain ⟨i, hi⟩ := hab (1 / ((n.toNat : ℚ) + 1)) (by positivity);
    refine' ⟨ RGFNat.ofNat' i, fun k hk => _ ⟩ ; specialize hi k.toNat ( by
      have h_toNat : ∀ (k : RGFNat), (ofNat' i).toNat ≤ k.toNat ↔ ofNat' i ≤ k := by
        exact fun k => by rw [ RGFNat.toNat_le ] ;
      exact h_toNat k |>.2 hk |> le_trans ( by simp +decide [ RGFNat.toNat_ofNat ] ) ; ) ; simp_all +decide [ RGFRat.isSmall_iff, RGFRat.toRat_sub ];
    grind +suggestions

/-
Build an RGF-Cauchy sequence from a standard `ℚ`-Cauchy sequence.
-/
theorem isRGFCauchy_ofRat_comp (f : CauSeq ℚ abs) :
    IsRGFCauchy (fun m => RGFRat.ofRat (f m.toNat)) := by
  intro n
  obtain ⟨i0, hi0⟩ : ∃ i0 : ℕ, ∀ k ≥ i0, |(f k : ℚ) - (f i0 : ℚ)| < 1 / ((n.toNat : ℚ) + 1) / 2 := by
    have := f.2 ( 1 / ( n.toNat + 1 ) / 2 ) ?_;
    · exact this;
    · positivity;
  use RGFNat.ofNat' i0; intro i j hi hj; simp_all +decide [ RGFRat.isSmall_iff, RGFRat.toRat_sub, RGFRat.toRat_ofRat ] ;
  grind +suggestions

theorem toReal_surjective : Function.Surjective toReal := by
  intro r
  induction' r using Real.ind_mk with f
  use Quotient.mk _ ⟨fun m => RGFRat.ofRat (f m.toNat), isRGFCauchy_ofRat_comp f⟩
  have h_eq : ∀ k, (cauSeqOf ⟨fun m => RGFRat.ofRat (f m.toNat), isRGFCauchy_ofRat_comp f⟩) k = f k := by
    simp +decide [ cauSeqOf_apply, RGFRat.toRat_ofRat, RGFNat.toNat_ofNat ]
  simp only [toReal_mk];
  exact congr_arg _ ( CauSeq.ext <| by aesop )

theorem toReal_bijective : Function.Bijective toReal :=
  ⟨toReal_injective, toReal_surjective⟩

/-- The bijection between RGF reals and the standard reals. -/
noncomputable def equivReal : RGFReal' ≃ ℝ :=
  Equiv.ofBijective toReal toReal_bijective

end RGFReal'
end RGF