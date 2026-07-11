/-
  Foundations/RGFNativeComplete.lean

  **Native** (from-scratch) Cauchy completeness of the RGF reals.

  The completeness theorem in `Foundations.RGFField` (`RGFReal'.complete`) is
  proved by transporting the problem to the *standard* reals `ℝ` (it invokes
  `cauchySeq_tendsto_of_complete`, i.e. the completeness of `ℝ`).  That derives
  completeness *from* `ℝ` rather than *inside* the RGF system.

  Here we prove Cauchy completeness **internally**, using only:
    * the native pointwise order `RGFReal'.leRel` / `≤` (from `RGFOrderReal`),
    * the rational layer `RGFRat` and the comparison map `RGFRat.toRat : RGFRat → ℚ`,
  and **never** the map `RGFReal'.toReal` or any completeness fact about `ℝ`.

  Strategy.  Smallness of an RGF real `x` at error level `k` (`Small x k`) is the
  pair of native inequalities `-1/(k+1) ≤ x ≤ 1/(k+1)`.  The keystone lemma
  `small_mk_iff` rewrites this, through the native order's definition, as a clean
  statement about the rational approximations of `x`.  All remaining analysis
  (triangle inequalities, the Cauchy property of the diagonal of rationals, and
  convergence) is then carried out at the level of `ℚ`, internal to the RGF tower.
-/
import Mathlib
import RGF.Math.Real.RGFNativeField
import RGF.Math.Real.RGFOrderReal

namespace RGF

open RGFNat RGFInt RGFRat

namespace RGFReal'

/-- A typed constructor of an RGF real from a Cauchy rational sequence (its result
    type is `RGFReal'`, so the field/`Sub` instances are found by `HSub`). -/
def mkReal (p : RGFNat → RGFRat) (hp : IsRGFCauchy p) : RGFReal' :=
  Quotient.mk PreReal.preRealSetoid ⟨p, hp⟩

theorem mkReal_eq (p : RGFNat → RGFRat) (hp : IsRGFCauchy p) :
    mkReal p hp = Quotient.mk PreReal.preRealSetoid ⟨p, hp⟩ := rfl

/-- The real error bound `1/(k+1)`, as an RGF real. -/
noncomputable def errR (k : RGFNat) : RGFReal' := ofRGFRat (RGFRat.oneDivSucc k)

/-- Negation commutes with the rational embedding. -/
theorem neg_ofRGFRat (q : RGFRat) : -ofRGFRat q = ofRGFRat (RGFRat.neg q) := by
  show neg (ofRGFRat q) = ofRGFRat (RGFRat.neg q)
  rfl

/-- `x` is small at level `k`: `-1/(k+1) ≤ x ≤ 1/(k+1)` in the native order. -/
def Small (x : RGFReal') (k : RGFNat) : Prop := -errR k ≤ x ∧ x ≤ errR k

/-
**Keystone reduction.** Native smallness of `⟦p⟧` is exactly a statement about
    the rational approximations of `p`: for every refinement level `m`, eventually
    `|toRat (p.approx j)| ≤ 1/(k+1) + 1/(m+1)`.
-/
theorem small_mk_iff (p : PreReal) (k : RGFNat) :
    Small (Quotient.mk PreReal.preRealSetoid p) k ↔
      ∀ m : RGFNat, ∃ N : RGFNat, ∀ j : RGFNat, N ≤ j →
        |RGFRat.toRat (p.approx j)| ≤ 1 / ((k.toNat : ℚ) + 1) + 1 / ((m.toNat : ℚ) + 1) := by
  constructor <;> intro h;
  · intro m
    obtain ⟨N₁, hN₁⟩ := h.left m
    obtain ⟨N₂, hN₂⟩ := h.right m
    use RGFNat.max N₁ N₂;
    intro j hj
    have h₁ := hN₁ j (by
    exact RGFNat.le_trans ( RGFNat.le_max_left _ _ ) hj)
    have h₂ := hN₂ j (by
    exact RGFNat.le_trans ( RGFNat.le_max_right _ _ ) hj);
    grind +suggestions;
  · constructor <;> rw [ RGFReal'.le_iff_leRel ];
    · intro m; obtain ⟨ N, hN ⟩ := h m; use N; intro j hj; simp_all +decide [ abs_le ] ;
      grind +suggestions;
    · convert RGF.PreReal.le_iff_rat p ⟨ fun _ => RGFRat.oneDivSucc k, IsRGFCauchy.const _ ⟩ |>.2 _;
      exact fun n => by obtain ⟨ N, hN ⟩ := h n; exact ⟨ N, fun j hj => le_trans ( le_abs_self _ ) ( hN j hj ) |> le_trans <| by simp +decide [ RGFRat.toRat_oneDivSucc ] ⟩ ;

/-
A real is approximable, at any level, by a rational (native).
-/
theorem real_approx_by_rat (x : RGFReal') (k : RGFNat) :
    ∃ q : RGFRat, Small (x - ofRGFRat q) k := by
  obtain ⟨ p, rfl ⟩ := Quotient.exists_rep x;
  obtain ⟨ N, hN ⟩ := p.cauchy k;
  refine' ⟨ p.approx N, _, _ ⟩;
  · convert small_mk_iff _ k |>.2 _ |>.1 using 1;
    intro m; use N; intro j hj; specialize hN j N hj ( by tauto ) ; rw [ RGFRat.isSmall_iff ] at hN;
    convert le_add_of_le_of_nonneg hN ( by positivity : ( 0 : ℚ ) ≤ 1 / ( m.toNat + 1 ) ) using 1;
  · convert small_mk_iff _ _ |>.2 _ |>.2 using 1;
    intro m; use N; intro j hj; specialize hN j N hj ( by tauto ) ; rw [ RGFRat.isSmall_iff ] at hN;
    convert le_add_of_le_of_nonneg hN ( by positivity : ( 0 : ℚ ) ≤ 1 / ( m.toNat + 1 ) ) using 1

/-
Negation preserves smallness.
-/
theorem small_neg {a : RGFReal'} {k : RGFNat} (ha : Small a k) : Small (-a) k := by
  obtain ⟨q, hq⟩ := Quotient.exists_rep a;
  -- By definition of negation, $-a$ is represented by the sequence of negations of the approximations of $a$.
  have h_neg : -a = Quotient.mk _ ⟨fun n => RGFRat.neg (q.approx n), q.cauchy.neg⟩ := by
    exact hq ▸ rfl;
  rw [h_neg];
  rw [ small_mk_iff ] at *;
  intro m; obtain ⟨ N, hN ⟩ := small_mk_iff q k |>.1 ( hq ▸ ha ) m; use N; intros j hj; specialize hN j hj; simp_all +decide ;
  grind +suggestions

/-
The rational embedding commutes with subtraction.
-/
theorem ofRGFRat_sub (a b : RGFRat) :
    ofRGFRat (a - b) = ofRGFRat a - ofRGFRat b := by
  -- Prove the pointwise identity in `RGFRat` first: the `HSub.hSub` operator is defined via `neg` and `add`, so for constant values `a, b`, we rewrite `a - b` as `a + neg b` (definitional equality) and then use `mk_eq_of_pointwise` to conclude equality of the constant sequences as `PreReal`, hence of their `Quotient.mk` results.
  exact mk_eq_of_pointwise _ _ fun _ => by
    simp [Sub.sub, HSub.hSub]

/-
Smallness of a constant real collapses to a clean rational inequality.
-/
theorem small_const (c : RGFRat) (k : RGFNat) :
    Small (ofRGFRat c) k ↔ |RGFRat.toRat c| ≤ 1 / ((k.toNat : ℚ) + 1) := by
  constructor <;> intro h;
  · have h_abs : ∀ m : RGFNat, |c.toRat| ≤ 1 / (k.toNat + 1 : ℚ) + 1 / (m.toNat + 1 : ℚ) := by
      intro m
      have h_small : Small (ofRGFRat c) k := h
      have h_abs : ∀ m : RGFNat, ∃ N : RGFNat, ∀ j : RGFNat, N ≤ j → |RGFRat.toRat (c)| ≤ 1 / (k.toNat + 1 : ℚ) + 1 / (m.toNat + 1 : ℚ) := by
        intro m
        have h_abs : Small (ofRGFRat c) k := h_small
        have h_abs : ∀ m : RGFNat, ∃ N : RGFNat, ∀ j : RGFNat, N ≤ j → |RGFRat.toRat (c)| ≤ 1 / (k.toNat + 1 : ℚ) + 1 / (m.toNat + 1 : ℚ) := by
          intro m
          have := small_mk_iff (⟨fun _ => c, IsRGFCauchy.const c⟩ : PreReal) k
          exact this.mp h_abs m
        exact h_abs m
      obtain ⟨N, hN⟩ := h_abs m
      specialize hN N (le_refl N)
      exact hN;
    -- By definition of `RGFRat.exists_index`, for any `ε > 0`, there exists `m` such that `1 / ((m.toNat : ℚ) + 1) ≤ ε`.
    have h_exists_index : ∀ ε > 0, ∃ m : RGFNat, 1 / ((m.toNat : ℚ) + 1) ≤ ε := by
      grind +suggestions;
    exact le_of_forall_pos_le_add fun ε hε => by obtain ⟨ m, hm ⟩ := h_exists_index ε hε; linarith [ h_abs m ] ;
  · convert small_mk_iff _ k |>.2 _;
    exact fun m => ⟨ 0, fun _ _ => le_add_of_le_of_nonneg h <| by positivity ⟩

/-
Triangle inequality for smallness: if `a` is small at level `ka` and `b` at
    level `kb`, and the rational error bounds add up to at most `1/(kc+1)`, then
    `a + b` is small at level `kc`.
-/
theorem small_add_of {a b : RGFReal'} {ka kb kc : RGFNat}
    (ha : Small a ka) (hb : Small b kb)
    (hlevel : 1 / ((ka.toNat : ℚ) + 1) + 1 / ((kb.toNat : ℚ) + 1)
              ≤ 1 / ((kc.toNat : ℚ) + 1)) :
    Small (a + b) kc := by
  obtain ⟨pa, rfl⟩ := Quotient.exists_rep a; obtain ⟨pb, rfl⟩ := Quotient.exists_rep b;
  convert small_mk_iff _ _ |>.2 _;
  intro m;
  obtain ⟨ m', hm' ⟩ := RGFRat.exists_index ( 1 / ( m.toNat + 1 ) / 2 ) ( by positivity );
  obtain ⟨ Na, hNa ⟩ := small_mk_iff _ _ |>.1 ha m'
  obtain ⟨ Nb, hNb ⟩ := small_mk_iff _ _ |>.1 hb m'
  use RGFNat.max Na Nb;
  intro j hj; specialize hNa j ( RGFNat.le_trans ( RGFNat.le_max_left _ _ ) hj ) ; specialize hNb j ( RGFNat.le_trans ( RGFNat.le_max_right _ _ ) hj ) ; simp_all +decide [ abs_le ] ;
  constructor <;> linarith [ RGFRat.toRat_add ( pa.approx j ) ( pb.approx j ) ]

/-
Ternary triangle inequality for smallness.
-/
theorem small_add3_of {a b c : RGFReal'} {ka kb kc kd : RGFNat}
    (ha : Small a ka) (hb : Small b kb) (hc : Small c kc)
    (hlevel : 1 / ((ka.toNat : ℚ) + 1) + 1 / ((kb.toNat : ℚ) + 1) + 1 / ((kc.toNat : ℚ) + 1)
              ≤ 1 / ((kd.toNat : ℚ) + 1)) :
    Small (a + b + c) kd := by
  obtain ⟨pa, hpa⟩ : ∃ pa : PreReal, a = Quotient.mk PreReal.preRealSetoid pa := by
    exact ⟨ Quotient.out a, Eq.symm <| Quotient.out_eq' a ⟩
  obtain ⟨pb, hpb⟩ : ∃ pb : PreReal, b = Quotient.mk PreReal.preRealSetoid pb := by
    exact ⟨ _, Eq.symm <| Quotient.out_eq' b ⟩
  obtain ⟨pc, hpc⟩ : ∃ pc : PreReal, c = Quotient.mk PreReal.preRealSetoid pc := by
    exact ⟨ _, Eq.symm <| Quotient.out_eq' _ ⟩;
  convert small_mk_iff _ _ |>.2 _;
  convert congr_arg₂ ( · + · ) ( congr_arg₂ ( · + · ) hpa hpb ) hpc using 1;
  intro m; obtain ⟨ m', hm' ⟩ := RGFRat.exists_index ( 1 / ( ( m.toNat : ℚ ) + 1 ) / 3 ) ( by positivity ) ; simp_all +decide [ abs_le ] ;
  obtain ⟨ Na, hNa ⟩ := small_mk_iff pa ka |>.1 ha m'
  obtain ⟨ Nb, hNb ⟩ := small_mk_iff pb kb |>.1 hb m'
  obtain ⟨ Nc, hNc ⟩ := small_mk_iff pc kc |>.1 hc m';
  refine' ⟨ RGFNat.max ( RGFNat.max Na Nb ) Nc, fun j hj => _ ⟩ ; simp_all +decide [ abs_le ];
  have := hNa j ( le_trans ( RGFNat.le_max_left _ _ ) ( le_trans ( RGFNat.le_max_left _ _ ) hj ) ) ; have := hNb j ( le_trans ( RGFNat.le_max_right _ _ ) ( le_trans ( RGFNat.le_max_left _ _ ) hj ) ) ; have := hNc j ( le_trans ( RGFNat.le_max_right _ _ ) hj ) ; norm_num [ RGFRat.toRat_add ] at * ; constructor <;> linarith;

/-
The rational approximations of a Cauchy rational sequence converge (natively)
    to the RGF real they define.
-/
theorem selfApprox_small (p : RGFNat → RGFRat) (hp : IsRGFCauchy p) (kb : RGFNat) :
    ∃ M : RGFNat, ∀ n : RGFNat, M ≤ n →
      Small (ofRGFRat (p n) - mkReal p hp) kb := by
  obtain ⟨ M, hM ⟩ := hp kb;
  use M;
  intro n hn;
  convert small_mk_iff _ _ |>.2 _;
  intro m; use M; intro j hj; specialize hM n j hn hj; simp_all +decide [ RGFRat.isSmall_iff ] ;
  convert le_add_of_le_of_nonneg hM ( by positivity : 0 ≤ ( m.toNat + 1 : ℚ ) ⁻¹ ) using 1

/-- A native Cauchy sequence of RGF reals. -/
def IsCauchy (s : ℕ → RGFReal') : Prop :=
  ∀ k : RGFNat, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → Small (s i - s j) k

/-- `s` converges natively to `L`. -/
def Converges (s : ℕ → RGFReal') (L : RGFReal') : Prop :=
  ∀ k : RGFNat, ∃ N : ℕ, ∀ i : ℕ, N ≤ i → Small (s i - L) k

/-
The diagonal rational sequence built from per-term rational approximations of
    a native Cauchy sequence is itself Cauchy.
-/
theorem rat_diagonal_cauchy (s : ℕ → RGFReal') (h : IsCauchy s)
    (q : ℕ → RGFRat) (hq : ∀ i, Small (s i - ofRGFRat (q i)) (RGFNat.ofNat' i)) :
    IsRGFCauchy (fun n => q n.toNat) := by
  intro lev
  obtain ⟨e, he⟩ : ∃ e : RGFNat, 1 / ((e.toNat : ℚ) + 1) ≤ (1 / ((lev.toNat : ℚ) + 1)) / 3 := by
    obtain ⟨ e, he ⟩ := RGFRat.exists_index ( 1 / ( lev.toNat + 1 ) / 3 ) ( by positivity );
    use e
  obtain ⟨Ns, hNs⟩ : ∃ Ns : ℕ, ∀ i j : ℕ, Ns ≤ i → Ns ≤ j → Small (s i - s j) e := by
    exact h e
  obtain ⟨Tq, hTq⟩ : ∃ Tq : ℕ, 1 / ((Tq : ℚ) + 1) ≤ (1 / ((lev.toNat : ℚ) + 1)) / 3 := by
    exact ⟨ e.toNat, he ⟩
  set T := Nat.max Ns Tq
  set N := RGFNat.ofNat' T;
  use N;
  intro i' j' hi hj
  set a := i'.toNat
  set b := j'.toNat
  have ha : a ≥ T := by
    exact le_trans ( by simp +decide [ N, RGFNat.toNat_ofNat ] ) ( RGFNat.toNat_le.1 hi )
  have hb : b ≥ T := by
    grind +suggestions
  have haNs : a ≥ Ns := by
    exact le_trans ( Nat.le_max_left _ _ ) ha
  have hbNs : b ≥ Ns := by
    exact le_trans ( Nat.le_max_left _ _ ) hb
  have haTq : a ≥ Tq := by
    exact le_trans ( Nat.le_max_right _ _ ) ha
  have hbTq : b ≥ Tq := by
    exact le_trans ( Nat.le_max_right _ _ ) hb;
  have h1 : Small (ofRGFRat (q a) - s a) (RGFNat.ofNat' a) := by
    convert small_neg ( hq a ) using 1;
    abel1
  have h2 : Small (s a - s b) e := by
    exact hNs a b haNs hbNs
  have h3 : Small (s b - ofRGFRat (q b)) (RGFNat.ofNat' b) := by
    exact hq b;
  have h4 : Small ((ofRGFRat (q a) - s a) + (s a - s b) + (s b - ofRGFRat (q b))) lev := by
    apply small_add3_of h1 h2 h3;
    convert add_le_add_three ( show ( 1 : ℚ ) / ( a + 1 ) ≤ 1 / ( lev.toNat + 1 ) / 3 from ?_ ) he ( show ( 1 : ℚ ) / ( b + 1 ) ≤ 1 / ( lev.toNat + 1 ) / 3 from ?_ ) using 1;
    · rw [ RGFNat.toNat_ofNat, RGFNat.toNat_ofNat ];
    · ring;
    · exact le_trans ( by gcongr ) hTq;
    · exact le_trans ( by gcongr ) hTq;
  convert small_const ( q a - q b ) lev |>.1 _ using 1;
  · convert RGFRat.isSmall_iff ( q a - q b ) lev using 1;
  · convert h4 using 1;
    rw [ ofRGFRat_sub ] ; ring

/-
The native limit of a Cauchy sequence is the RGF real given by its diagonal
    rational sequence.
-/
theorem rat_diagonal_converges (s : ℕ → RGFReal')
    (q : ℕ → RGFRat) (hq : ∀ i, Small (s i - ofRGFRat (q i)) (RGFNat.ofNat' i))
    (hp : IsRGFCauchy (fun n => q n.toNat)) :
    Converges s (mkReal (fun n => q n.toNat) hp) := by
  intro k;
  obtain ⟨b, hb⟩ : ∃ b : RGFNat, 1 / ((b.toNat : ℚ) + 1) ≤ (1 / ((k.toNat : ℚ) + 1)) / 2 := by
    convert RGFRat.exists_index ( 1 / ( k.toNat + 1 ) / 2 ) ( by positivity ) using 1;
  obtain ⟨ M, hM ⟩ := selfApprox_small ( fun n => q n.toNat ) hp b;
  refine' ⟨ Max.max b.toNat M.toNat, fun i hi => _ ⟩ ; have := hq i ; have := hM ( RGFNat.ofNat' i ) ?_ <;> simp_all +decide [ RGFReal'.Small ];
  · -- Apply the small_add_of lemma with the level inequality.
    have hlevel : 1 / ((ofNat' i).toNat + 1 : ℚ) + 1 / ((b.toNat + 1 : ℚ)) ≤ 1 / ((k.toNat + 1 : ℚ)) := by
      norm_num [ RGFNat.ofNat' ] at *;
      rw [ RGFNat.toNat_ofNat ] ; linarith [ inv_anti₀ ( by positivity ) ( show ( i : ℚ ) + 1 ≥ b.toNat + 1 by norm_cast; linarith ) ];
    convert small_add_of ( hq i ) this hlevel using 1 ; ring;
    unfold Small; ring;
    rw [ show ( ofNat' i ).toNat = i from RGFNat.toNat_ofNat i ] ; ring;
  · grind +suggestions

/-- **Native Cauchy completeness of the RGF reals.** Every native Cauchy
    sequence of RGF reals converges to some RGF real, proved without transport
    through the standard reals `ℝ`. -/
theorem complete_native (s : ℕ → RGFReal') (h : IsCauchy s) :
    ∃ L : RGFReal', Converges s L := by
  choose q hq using fun i => real_approx_by_rat (s i) (RGFNat.ofNat' i)
  exact ⟨mkReal (fun n => q n.toNat) (rat_diagonal_cauchy s h q hq),
         rat_diagonal_converges s q hq _⟩

end RGFReal'
end RGF