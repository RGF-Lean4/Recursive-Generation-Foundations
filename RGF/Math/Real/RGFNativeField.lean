/-
  Foundations/RGFNativeField.lean

  **Native** (from-scratch) proofs of the field axioms for the RGF reals.

  The file `Foundations.RGFField` proves the field axioms of `RGFReal'` by
  transporting them through the ring isomorphism `RGFReal' ≃+* ℝ` with the
  *standard* reals.  Mathematically this is sound, but it derives the core
  algebraic facts *from* the standard reals rather than *inside* the RGF system.

  Here every commutative-ring axiom is proved **internally**: each statement is
  reduced (via `Quotient.ind`/`Quotient.sound`) to the corresponding pointwise
  identity on `RGFRat`, which in turn rests only on the native `CommRing RGFInt`
  structure.  No appeal to `RGFReal'.toReal` or to `ℝ` is made anywhere in this
  file's ring-axiom proofs; the only "outside" objects used are the rationals
  `ℚ` already employed throughout the RGF Cauchy machinery (never the reals).
-/
import Mathlib
import RGF.Math.Real.RGFReal

namespace RGF

open RGFNat RGFInt RGFRat

namespace RGFReal'

/-- Two RGF reals given by pointwise-equal approximating sequences are equal.
    This is the bridge that turns a pointwise `RGFRat` identity into an identity
    of RGF reals, with no reference to the standard reals. -/
theorem mk_eq_of_pointwise (x y : PreReal) (h : ∀ k, x.approx k = y.approx k) :
    (Quotient.mk PreReal.preRealSetoid x) = (Quotient.mk PreReal.preRealSetoid y) := by
  apply Quotient.sound
  intro n
  refine ⟨0, fun k _ => ?_⟩
  rw [RGFRat.isSmall_iff, h k, RGFRat.toRat_sub, sub_self, abs_zero]
  positivity

/-! ## Additive group axioms (native) -/

theorem nat_add_assoc (a b c : RGFReal') : a + b + c = a + (b + c) := by
  obtain ⟨ x, rfl ⟩ := Quotient.exists_rep a;
  obtain ⟨ y, rfl ⟩ := Quotient.exists_rep b;
  induction' c using Quotient.inductionOn' with z;
  apply mk_eq_of_pointwise
  intro k
  exact RGFRat.add_assoc _ _ _

theorem nat_add_comm (a b : RGFReal') : a + b = b + a := by
  obtain ⟨ x, hx ⟩ := Quotient.exists_rep a;
  obtain ⟨ y, hy ⟩ := Quotient.exists_rep b;
  rw [ ← hx, ← hy ];
  convert mk_eq_of_pointwise _ _ _;
  exact fun k => RGFRat.add_comm _ _

theorem nat_zero_add (a : RGFReal') : 0 + a = a := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  convert mk_eq_of_pointwise _ _ _
  exact fun k => RGFRat.zero_add _

theorem nat_add_zero (a : RGFReal') : a + 0 = a := by
  convert nat_add_comm a 0 |> Eq.trans <| nat_zero_add a using 1

theorem nat_neg_add_cancel (a : RGFReal') : neg a + a = 0 := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  convert mk_eq_of_pointwise _ _ _
  exact fun k => RGFRat.neg_add_cancel _

theorem nat_add_neg_cancel (a : RGFReal') : a + neg a = 0 := by
  obtain ⟨ x, hx ⟩ := a;
  convert mk_eq_of_pointwise _ _ _;
  -- By definition of addition in the rationals, we have $x k + (-x k) = 0$.
  simp [RGFRat.add_neg_cancel];
  rfl

/-! ## Multiplicative monoid + distributivity axioms (native) -/

theorem nat_mul_assoc (a b c : RGFReal') : a * b * c = a * (b * c) := by
  induction a using Quotient.ind;
  induction b using Quotient.ind;
  induction c using Quotient.ind;
  apply mk_eq_of_pointwise; intro k; exact RGFRat.mul_assoc _ _ _

theorem nat_mul_comm (a b : RGFReal') : a * b = b * a := by
  -- To prove that multiplication in RGFReal' is commutative, we reduced the goal to showing
  -- that the product of the underlying Cauchy approximations is pointwise commutative.
  induction a using Quotient.ind with | _ x =>
    induction b using Quotient.ind with | _ y =>
      show mul _ _ = mul _ _;
      unfold mul;
      simp only [Quotient.lift₂_mk];
      apply mk_eq_of_pointwise;
      intro k;
      exact RGFRat.mul_comm (x.approx k) (y.approx k)

theorem nat_one_mul (a : RGFReal') : 1 * a = a := by
  obtain ⟨ x, hx ⟩ := a;
  convert mk_eq_of_pointwise _ _ _;
  exact fun k => RGFRat.one_mul _

theorem nat_mul_one (a : RGFReal') : a * 1 = a := by
  -- By definition of multiplication in the real numbers, multiplying by 1 leaves the number unchanged.
  apply Eq.symm; exact (by
    have := nat_one_mul a;
    rw [ ← nat_mul_comm, this ])

theorem nat_left_distrib (a b c : RGFReal') : a * (b + c) = a * b + a * c := by
  obtain ⟨a₁, a₂⟩ := a;
  obtain ⟨b₁, b₂⟩ := b;
  obtain ⟨c₁, c₂⟩ := c;
  convert mk_eq_of_pointwise _ _ _ using 1;
  grind +suggestions

theorem nat_right_distrib (a b c : RGFReal') : (a + b) * c = a * c + b * c := by
  grind +suggestions

theorem nat_zero_mul (a : RGFReal') : 0 * a = 0 := by
  convert RGFReal'.mk_eq_of_pointwise _ _ _;
  convert rfl;
  rotate_left;
  exact ⟨ fun _ => RGFRat.zero, IsRGFCauchy.const RGFRat.zero ⟩;
  · exact fun _ => rfl;
  · induction a using Quotient.ind;
    convert RGFReal'.mk_eq_of_pointwise _ _ _;
    exact fun k => Eq.symm ( RGFRat.zero_mul _ )

theorem nat_mul_zero (a : RGFReal') : a * 0 = 0 := by
  convert nat_zero_mul a using 1;
  rw [ nat_mul_comm ]

theorem nat_zero_ne_one : (0 : RGFReal') ≠ 1 := by
  intro h;
  -- By definition of equivalence, we know that if $0 = 1$, then for any $n$, $0 - 1$ is small.
  have h_equiv : ∀ n : RGFNat, RGFRat.isSmall (RGFRat.zero - RGFRat.one) n := by
    convert Quotient.exact h using 1;
    constructor <;> intro h <;> have := h 0 <;> simp_all +decide ;
    · convert h using 1;
      constructor <;> intro h;
      · assumption;
      · exact fun n => ⟨ 0, fun k hk => h n ⟩;
    · exact fun n => by obtain ⟨ N, hN ⟩ := this; exact h n |> fun h => by tauto;
  convert RGFRat.isSmall_iff ( RGFRat.zero - RGFRat.one ) 2 using 1 ; norm_num [ RGFRat.toRat_sub, RGFRat.toRat_zero, RGFRat.toRat_one ];
  exact fun h => absurd ( h.mp ( h_equiv 2 ) ) ( by native_decide )

/-! ## Multiplicative inverse (native)

We build the multiplicative inverse of a nonzero RGF real *internally*, i.e.
without the ring isomorphism `RGFReal' ≃+* ℝ`.  The construction inverts the
rational approximations coordinate-wise (using only the rational layer `RGFRat`
and the comparison map `RGFRat.toRat : RGFRat → ℚ`, never the reals), after
showing that a nonzero real is eventually bounded away from `0`. -/

open Classical in
/-- Coordinate-wise rational inverse: `0` is sent to `0`, every other rational to
    its genuine inverse.  Stays entirely inside the rational layer. -/
noncomputable def rinv (q : RGFRat) : RGFRat :=
  if RGFRat.toRat q = 0 then 0 else RGFRat.ofRat (RGFRat.toRat q)⁻¹

theorem toRat_rinv (q : RGFRat) : RGFRat.toRat (rinv q) = (RGFRat.toRat q)⁻¹ := by
  unfold rinv
  split
  case isTrue h => simp [h, RGFRat.toRat_zero]
  case isFalse h => rw [RGFRat.toRat_ofRat]

/-
A nonzero RGF real, viewed through any representative, is eventually bounded
    away from `0` in `ℚ` (through `toRat`).
-/
theorem nonzero_boundedAway (a : RGFReal') (ha : a ≠ 0) :
    ∃ (c : ℚ) (N : RGFNat), 0 < c ∧
      ∀ k : RGFNat, N ≤ k → c ≤ |RGFRat.toRat ((Quotient.out a).approx k)| := by
  contrapose! ha with h;
  rw [ ← Quotient.out_eq a ];
  refine' Quotient.sound _;
  intro n
  obtain ⟨N, hN⟩ : ∃ N : RGFNat, ∀ i j : RGFNat, N ≤ i → N ≤ j → |RGFRat.toRat ((Quotient.out a).approx i) - RGFRat.toRat ((Quotient.out a).approx j)| ≤ 1 / ((n.toNat : ℚ) + 1) / 2 := by
    obtain ⟨ m, hm ⟩ := RGFRat.exists_index ( 1 / ( n.toNat + 1 ) / 2 ) ( by positivity );
    have := ( Quotient.out a ).cauchy m;
    obtain ⟨ N, hN ⟩ := this; use N; intro i j hi hj; specialize hN i j hi hj; rw [ RGFRat.isSmall_iff ] at hN; simp_all +decide [ RGFRat.toRat_sub ] ;
    exact hN.trans hm;
  obtain ⟨ k, hk₁, hk₂ ⟩ := h ( 1 / ( n.toNat + 1 ) / 2 ) N ( by positivity );
  use k;
  intro m hm; rw [ RGFRat.isSmall_iff ] ; simp_all +decide [ abs_le ] ;
  constructor <;> linarith! [ abs_lt.mp hk₂, hN k m hk₁ ( le_trans hk₁ hm ), RGFRat.toRat_sub ( ( Quotient.out a ).approx m ) RGFRat.zero, RGFRat.toRat_zero ]

/-
The coordinate-wise inverse of a nonzero real's representative is Cauchy.
-/
theorem invSeq_cauchy (a : RGFReal') (ha : a ≠ 0) :
    IsRGFCauchy (fun k => rinv ((Quotient.out a).approx k)) := by
  obtain ⟨c, N₀, hc, hN₀⟩ := nonzero_boundedAway a ha;
  intro n
  obtain ⟨m, hm⟩ := RGFRat.exists_index (1 / ((n.toNat : ℚ) + 1) * c^2) (by
  positivity)
  obtain ⟨N₁, hN₁⟩ := (Quotient.out a).cauchy m
  use RGFNat.max N₀ N₁
  intro i j hi hj
  have h_abs : |RGFRat.toRat ((Quotient.out a).approx i) - RGFRat.toRat ((Quotient.out a).approx j)| ≤ 1 / ((m.toNat : ℚ) + 1) := by
    convert hN₁ i j ( RGFNat.le_trans ( RGFNat.le_max_right _ _ ) hi ) ( RGFNat.le_trans ( RGFNat.le_max_right _ _ ) hj ) using 1;
    simp +decide [ RGFRat.isSmall_iff, RGFRat.toRat_sub ];
  have h_inv_abs : |(RGFRat.toRat ((Quotient.out a).approx i))⁻¹ - (RGFRat.toRat ((Quotient.out a).approx j))⁻¹| ≤ |RGFRat.toRat ((Quotient.out a).approx i) - RGFRat.toRat ((Quotient.out a).approx j)| / c^2 := by
    rw [ inv_sub_inv, abs_div ];
    · rw [ abs_sub_comm, abs_mul ];
      gcongr;
      exact le_trans ( by nlinarith ) ( mul_le_mul ( hN₀ i ( RGFNat.le_max_left _ _ |> RGFNat.le_trans <| hi ) ) ( hN₀ j ( RGFNat.le_max_left _ _ |> RGFNat.le_trans <| hj ) ) ( by positivity ) ( by positivity ) );
    · exact fun h => by have := hN₀ i ( le_trans ( RGFNat.le_max_left _ _ ) hi ) ; norm_num [ h ] at this; linarith;
    · exact fun h => by have := hN₀ j ( le_trans ( RGFNat.le_max_left _ _ ) hj ) ; norm_num [ h ] at this; linarith;
  have h_inv_abs_le : |(RGFRat.toRat ((Quotient.out a).approx i))⁻¹ - (RGFRat.toRat ((Quotient.out a).approx j))⁻¹| ≤ 1 / ((n.toNat : ℚ) + 1) := by
    exact h_inv_abs.trans ( by rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith );
  grind +suggestions

open Classical in
/-- The native multiplicative inverse on `RGFReal'`. -/
noncomputable def natInv (a : RGFReal') : RGFReal' :=
  if h : a = 0 then 0
  else Quotient.mk _ ⟨fun k => rinv ((Quotient.out a).approx k), invSeq_cauchy a h⟩

/-
**Native `mul_inv_cancel`.** Every nonzero RGF real has the constructed
    inverse, proved without transport through `ℝ`.
-/
theorem nat_mul_inv_cancel (a : RGFReal') (ha : a ≠ 0) : a * natInv a = 1 := by
  obtain ⟨c, N, hc, hN⟩ : ∃ (c : ℚ) (N : RGFNat), 0 < c ∧ ∀ k : RGFNat, N ≤ k → c ≤ |RGFRat.toRat ((Quotient.out a).approx k)| := nonzero_boundedAway a ha;
  rw [ ← Quotient.out_eq a ];
  rw [ natInv ];
  split_ifs ; simp_all +decide;
  erw [ Quotient.eq ];
  intro n; use N; intro k hk; simp +decide [ RGFRat.isSmall_iff, RGFRat.toRat_sub, RGFRat.toRat_mul, toRat_rinv ] ;
  rw [ mul_inv_cancel₀ ( by specialize hN k hk; contrapose! hN; aesop ) ] ; norm_num [ RGFRat.one ];
  erw [ RGFRat.toRat_ofRGFInt ];
  erw [ RGFInt.toInt_one ] ; norm_num;
  positivity

/-- `natInv 0 = 0`, the boundary case of the native inverse. -/
theorem natInv_zero : natInv (0 : RGFReal') = 0 := by
  unfold natInv; rw [dif_pos rfl]

noncomputable instance : Inv RGFReal' := ⟨natInv⟩

theorem nat_inv_zero : (0 : RGFReal')⁻¹ = 0 := natInv_zero

theorem nat_mul_inv_cancel' (a : RGFReal') (ha : a ≠ 0) : a * a⁻¹ = 1 :=
  nat_mul_inv_cancel a ha

/-- **The RGF reals form a field — proved entirely natively.**

    Every axiom fed to `Field.ofMinimalAxioms` is one of the from-scratch
    theorems above (`nat_add_assoc`, `nat_zero_add`, `nat_neg_add_cancel`,
    `nat_mul_assoc`, `nat_mul_comm`, `nat_one_mul`, `nat_mul_inv_cancel'`,
    `nat_inv_zero`, `nat_left_distrib`, `nat_zero_ne_one`).  None of them is
    obtained by transporting a fact about the standard reals `ℝ`; the field
    structure is derived inside the RGF system itself. -/
noncomputable instance instField : Field RGFReal' :=
  Field.ofMinimalAxioms RGFReal'
    nat_add_assoc
    nat_zero_add
    nat_neg_add_cancel
    nat_mul_assoc
    nat_mul_comm
    nat_one_mul
    nat_mul_inv_cancel'
    nat_inv_zero
    nat_left_distrib
    ⟨0, 1, nat_zero_ne_one⟩

end RGFReal'
end RGF