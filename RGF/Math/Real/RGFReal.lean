/-
  Foundations/RGFReal.lean

  RGF reals: a construction based on Cauchy sequences of `RGFRat`, indexed by
  `RGFNat` (not the built-in `ℕ`).

  The "smallness" predicate `RGFRat.isSmall q n` (`|q| ≤ 1/(n+1)`) is defined in
  `Foundations.RGFOrder`. Here we build the type `RGFReal'` as the quotient of
  `RGFNat`-indexed Cauchy sequences, with addition, negation and multiplication
  proven to be well defined on equivalence classes (the well-definedness is
  reduced to ordinary `ℚ`-analysis through the ring map `RGFRat.toRat`).

  Dependency note: `import Mathlib` is used for tactic support; the core
  *definitions* do not depend on Mathlib's reals or analysis library.
-/
import Mathlib
import RGF.Math.Real.RGFOrder

namespace RGF

open RGFNat RGFInt RGFRat

/-! ## Archimedean index lemma -/

/-
For any positive rational `ε` there is an RGF index `n` with `1/(n+1) ≤ ε`.
-/
theorem RGFRat.exists_index (ε : ℚ) (hε : 0 < ε) :
    ∃ n : RGFNat, 1 / ((n.toNat : ℚ) + 1) ≤ ε := by
  -- By the Archimedean property, there exists a natural number $n$ such that $n > \frac{1}{\epsilon}$.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n > 1 / ε := by
    exact exists_nat_gt _;
  use RGFNat.ofNat' n;
  rw [ div_le_iff₀ ] <;> nlinarith [ mul_div_cancel₀ 1 hε.ne', show ( ofNat' n |> RGFNat.toNat : ℚ ) = n from mod_cast RGFNat.toNat_ofNat n ]

/-! ## Cauchy sequences indexed by RGFNat -/

/-- The Cauchy property of an `RGFRat` sequence (indexed by `RGFNat`). -/
def IsRGFCauchy (f : RGFNat → RGFRat) : Prop :=
  ∀ n : RGFNat, ∃ N : RGFNat, ∀ i j : RGFNat,
    N ≤ i → N ≤ j → RGFRat.isSmall (f i - f j) n

/-
A Cauchy sequence is eventually bounded (in `ℚ`, through `toRat`).
-/
theorem IsRGFCauchy.bddTail {f : RGFNat → RGFRat} (hf : IsRGFCauchy f) :
    ∃ (N : RGFNat) (B : ℚ), 0 ≤ B ∧ ∀ i : RGFNat, N ≤ i → |RGFRat.toRat (f i)| ≤ B := by
  obtain ⟨ N, hN ⟩ := hf RGFNat.zero;
  refine' ⟨ N, |( f N |> RGFRat.toRat )| + 1, by positivity, fun i hi => _ ⟩;
  have h_abs : |(f i).toRat - (f N).toRat| ≤ 1 := by
    convert hN i N hi ( RGFNat.le_refl N ) using 1;
    rw [ RGFRat.isSmall_iff ];
    rw [ RGFRat.toRat_sub ] ; norm_num;
  cases abs_cases ( ( f i |> RGFRat.toRat ) - ( f N |> RGFRat.toRat ) ) <;> cases abs_cases ( ( f i |> RGFRat.toRat ) ) <;> cases abs_cases ( ( f N |> RGFRat.toRat ) ) <;> linarith

theorem IsRGFCauchy.add {f g : RGFNat → RGFRat}
    (hf : IsRGFCauchy f) (hg : IsRGFCauchy g) :
    IsRGFCauchy (fun n => f n + g n) := by
  intro n;
  obtain ⟨ m, hm ⟩ := RGFRat.exists_index ( 1 / ( ( n.toNat : ℚ ) + 1 ) / 2 ) ( by positivity );
  obtain ⟨ N1, hN1 ⟩ := hf m
  obtain ⟨ N2, hN2 ⟩ := hg m
  use RGFNat.max N1 N2;
  intro i j hi hj; simp_all +decide [ RGFRat.isSmall_iff, RGFRat.toRat_sub, RGFRat.toRat_add ] ;
  exact abs_le.mpr ⟨ by linarith [ abs_le.mp ( hN1 i j ( RGFNat.le_trans ( RGFNat.le_max_left _ _ ) hi ) ( RGFNat.le_trans ( RGFNat.le_max_left _ _ ) hj ) ), abs_le.mp ( hN2 i j ( RGFNat.le_trans ( RGFNat.le_max_right _ _ ) hi ) ( RGFNat.le_trans ( RGFNat.le_max_right _ _ ) hj ) ) ], by linarith [ abs_le.mp ( hN1 i j ( RGFNat.le_trans ( RGFNat.le_max_left _ _ ) hi ) ( RGFNat.le_trans ( RGFNat.le_max_left _ _ ) hj ) ), abs_le.mp ( hN2 i j ( RGFNat.le_trans ( RGFNat.le_max_right _ _ ) hi ) ( RGFNat.le_trans ( RGFNat.le_max_right _ _ ) hj ) ) ] ⟩

theorem IsRGFCauchy.neg {f : RGFNat → RGFRat} (hf : IsRGFCauchy f) :
    IsRGFCauchy (fun n => RGFRat.neg (f n)) := by
  intro n; obtain ⟨ N, hN ⟩ := hf n; use N; intros i j hi hj; specialize hN i j hi hj; simp_all +decide [ RGFRat.isSmall_iff, RGFRat.toRat_sub, RGFRat.toRat_neg ] ;
  exact Eq.trans_le ( by rw [ neg_add_eq_sub, abs_sub_comm ] ) hN

theorem IsRGFCauchy.mul {f g : RGFNat → RGFRat}
    (hf : IsRGFCauchy f) (hg : IsRGFCauchy g) :
    IsRGFCauchy (fun n => f n * g n) := by
  intro n;
  -- Use the bounds from the Cauchy property and the Archimedean property to find such an N.
  obtain ⟨Nf, Bf, hBf⟩ := IsRGFCauchy.bddTail hf
  obtain ⟨Ng, Bg, hBg⟩ := IsRGFCauchy.bddTail hg
  set B := Bf + Bg + 1 with hB
  obtain ⟨m, hm⟩ := RGFRat.exists_index (1 / ((n.toNat : ℚ) + 1) / (2 * B)) (by
  exact div_pos ( by positivity ) ( mul_pos zero_lt_two ( by linarith ) ));
  obtain ⟨Nf', hNf'⟩ := hf m
  obtain ⟨Ng', hNg'⟩ := hg m
  use RGFNat.max (RGFNat.max Nf Ng) (RGFNat.max Nf' Ng');
  intro i j hi hj
  have h_bound : |(f i).toRat * (g i).toRat - (f j).toRat * (g j).toRat| ≤ B * (1 / ((m.toNat : ℚ) + 1)) + (1 / ((m.toNat : ℚ) + 1)) * B := by
    have h_bound : |(f i).toRat * (g i).toRat - (f j).toRat * (g j).toRat| ≤ |(f i).toRat| * |(g i).toRat - (g j).toRat| + |(f i).toRat - (f j).toRat| * |(g j).toRat| := by
      rw [ ← abs_mul, ← abs_mul ];
      cases abs_cases ( ( f i |> RGFRat.toRat ) * ( g i |> RGFRat.toRat ) - ( f j |> RGFRat.toRat ) * ( g j |> RGFRat.toRat ) ) <;> cases abs_cases ( ( f i |> RGFRat.toRat ) * ( ( g i |> RGFRat.toRat ) - ( g j |> RGFRat.toRat ) ) ) <;> cases abs_cases ( ( ( f i |> RGFRat.toRat ) - ( f j |> RGFRat.toRat ) ) * ( g j |> RGFRat.toRat ) ) <;> linarith;
    have h_bound : |(g i).toRat - (g j).toRat| ≤ 1 / ((m.toNat : ℚ) + 1) ∧ |(f i).toRat - (f j).toRat| ≤ 1 / ((m.toNat : ℚ) + 1) := by
      apply And.intro;
      · convert RGFRat.isSmall_iff ( g i - g j ) m |>.1 ( hNg' i j ( by exact le_trans ( by exact RGFNat.le_max_right _ _ |> RGFNat.le_trans <| RGFNat.le_max_right _ _ ) hi ) ( by exact le_trans ( by exact RGFNat.le_max_right _ _ |> RGFNat.le_trans <| RGFNat.le_max_right _ _ ) hj ) ) using 1;
        rw [ RGFRat.toRat_sub ];
      · have := hNf' i j ( by
          exact le_trans ( le_max_left _ _ ) ( le_trans ( le_max_right _ _ ) hi ) ) ( by
          exact le_trans ( le_max_left _ _ ) ( le_trans ( le_max_right _ _ ) hj ) );
        convert RGFRat.isSmall_iff _ _ |>.1 this using 1;
        rw [ RGFRat.toRat_sub ];
    have h_bound : |(f i).toRat| ≤ Bf ∧ |(g j).toRat| ≤ Bg := by
      exact ⟨ hBf.2 i ( le_trans ( RGFNat.le_max_left _ _ ) ( le_trans ( RGFNat.le_max_left _ _ ) hi ) ), hBg.2 j ( le_trans ( RGFNat.le_max_right _ _ ) ( le_trans ( RGFNat.le_max_left _ _ ) hj ) ) ⟩;
    nlinarith [ abs_nonneg ( ( f i |> RGFRat.toRat ) ), abs_nonneg ( ( g i |> RGFRat.toRat ) - ( g j |> RGFRat.toRat ) ), abs_nonneg ( ( f i |> RGFRat.toRat ) - ( f j |> RGFRat.toRat ) ), abs_nonneg ( ( g j |> RGFRat.toRat ) ), one_div_pos.mpr ( by positivity : 0 < ( m.toNat : ℚ ) + 1 ) ];
  rw [ RGFRat.isSmall_iff ];
  convert h_bound.trans _ using 1;
  · simp +decide [ RGFRat.toRat_sub, RGFRat.toRat_mul ];
  · rw [ le_div_iff₀ ] at hm <;> nlinarith [ show 0 < B by exact add_pos_of_nonneg_of_pos ( add_nonneg hBf.1 hBg.1 ) zero_lt_one ]

theorem IsRGFCauchy.const (q : RGFRat) : IsRGFCauchy (fun _ => q) := by
  intro n
  exact ⟨RGFNat.zero, fun i j _ _ => by
    simpa [RGFRat.isSmall_iff, RGFRat.toRat_sub] using
      (by positivity : (0:ℚ) ≤ 1 / ((n.toNat : ℚ) + 1))⟩

/-! ## Sequence-level equivalence -/

/-- Two `RGFRat` sequences are equivalent: their difference is eventually small. -/
def SeqEquiv (f g : RGFNat → RGFRat) : Prop :=
  ∀ n : RGFNat, ∃ N : RGFNat, ∀ k : RGFNat,
    N ≤ k → RGFRat.isSmall (f k - g k) n

theorem SeqEquiv.refl (f : RGFNat → RGFRat) : SeqEquiv f f := by
  intro n
  use 0;
  intro k hk; rw [ RGFRat.isSmall_iff ] ; norm_num [ RGFRat.toRat_sub, RGFRat.toRat_zero ] ;
  positivity

theorem SeqEquiv.symm {f g : RGFNat → RGFRat} (h : SeqEquiv f g) : SeqEquiv g f := by
  intro n
  obtain ⟨N, hN⟩ := h n
  use N
  intro k hk
  have h_abs : |RGFRat.toRat (g k - f k)| = |RGFRat.toRat (f k - g k)| := by
    grind +suggestions;
  exact RGFRat.isSmall_iff _ _ |>.2 ( h_abs.symm ▸ RGFRat.isSmall_iff _ _ |>.1 ( hN k hk ) )

theorem SeqEquiv.trans {f g h : RGFNat → RGFRat}
    (h1 : SeqEquiv f g) (h2 : SeqEquiv g h) : SeqEquiv f h := by
  intro n;
  -- Let ε := 1/((n.toNat:ℚ)+1) > 0.
  set ε : ℚ := 1 / ((n.toNat : ℚ) + 1) with hε_def;
  obtain ⟨m, hm⟩ : ∃ m : RGFNat, 1 / ((m.toNat : ℚ) + 1) ≤ ε / 2 := by
    have := RGFRat.exists_index ( ε / 2 ) ( by positivity ) ; aesop;
  obtain ⟨N1, hN1⟩ := h1 m
  obtain ⟨N2, hN2⟩ := h2 m
  use RGFNat.max N1 N2;
  intro k hk
  have h_diff : |RGFRat.toRat (f k) - RGFRat.toRat (h k)| ≤ |RGFRat.toRat (f k) - RGFRat.toRat (g k)| + |RGFRat.toRat (g k) - RGFRat.toRat (h k)| := by
    exact abs_sub_le _ _ _;
  grind +suggestions

theorem SeqEquiv.add {f₁ f₂ g₁ g₂ : RGFNat → RGFRat}
    (hf : SeqEquiv f₁ f₂) (hg : SeqEquiv g₁ g₂) :
    SeqEquiv (fun n => f₁ n + g₁ n) (fun n => f₂ n + g₂ n) := by
  intro n;
  obtain ⟨ m, hm ⟩ := RGFRat.exists_index ( 1 / ( ( n.toNat : ℚ ) + 1 ) / 2 ) ( by positivity );
  obtain ⟨ N₁, hN₁ ⟩ := hf m
  obtain ⟨ N₂, hN₂ ⟩ := hg m
  use RGFNat.max N₁ N₂;
  intro k hk; specialize hN₁ k ( RGFNat.le_trans ( RGFNat.le_max_left _ _ ) hk ) ; specialize hN₂ k ( RGFNat.le_trans ( RGFNat.le_max_right _ _ ) hk ) ; rw [ RGFRat.isSmall_iff ] at *; simp_all +decide [ RGFRat.toRat_sub, RGFRat.toRat_add ] ;
  exact abs_le.mpr ⟨ by linarith [ abs_le.mp hN₁, abs_le.mp hN₂ ], by linarith [ abs_le.mp hN₁, abs_le.mp hN₂ ] ⟩

theorem SeqEquiv.neg {f g : RGFNat → RGFRat} (h : SeqEquiv f g) :
    SeqEquiv (fun n => RGFRat.neg (f n)) (fun n => RGFRat.neg (g n)) := by
  intro n
  obtain ⟨N, hN⟩ := h n
  use N
  intro k hk
  have : RGFRat.toRat (( RGFRat.neg (f k) ) - ( RGFRat.neg (g k) )) = - (RGFRat.toRat (f k - g k)) := by
    rw [ RGFRat.toRat_sub, RGFRat.toRat_neg, RGFRat.toRat_neg, RGFRat.toRat_sub ] ; ring!;
  have := hN k hk; simp_all +decide [ RGFRat.isSmall_iff ] ;

theorem SeqEquiv.mul {f₁ f₂ g₁ g₂ : RGFNat → RGFRat}
    (hf₁ : IsRGFCauchy f₁) (hg₂ : IsRGFCauchy g₂)
    (hf : SeqEquiv f₁ f₂) (hg : SeqEquiv g₁ g₂) :
    SeqEquiv (fun n => f₁ n * g₁ n) (fun n => f₂ n * g₂ n) := by
  intro n
  obtain ⟨Na, Ba, hBa⟩ := hf₁.bddTail
  obtain ⟨Nd, Bd, hBd⟩ := hg₂.bddTail
  set B := Ba + Bd + 1
  have hB_pos : 0 < B := by
    linarith
  obtain ⟨m, hm⟩ := RGFRat.exists_index (1 / ((n.toNat : ℚ) + 1) / (2 * B)) (by
  positivity);
  obtain ⟨N1, hN1⟩ := hf m
  obtain ⟨N2, hN2⟩ := hg m
  use RGFNat.max (RGFNat.max Na Nd) (RGFNat.max N1 N2);
  intro k hk; rw [ RGFRat.isSmall_iff ] ; simp_all +decide [ div_eq_mul_inv ] ;
  -- Use the identity $f₁g₁ - f₂g₂ = f₁(g₁ - g₂) + (f₁ - f₂)g₂$.
  have h_identity : (f₁ k * g₁ k - f₂ k * g₂ k).toRat = (f₁ k).toRat * ((g₁ k - g₂ k).toRat) + ((f₁ k - f₂ k).toRat) * (g₂ k).toRat := by
    simp +decide [ RGFRat.toRat_sub, RGFRat.toRat_mul ] ; ring;
  -- Use the bounds on $f₁$ and $g₂$ to bound the terms.
  have h_bounds : |(f₁ k).toRat| ≤ Ba ∧ |(g₂ k).toRat| ≤ Bd ∧ |(f₁ k - f₂ k).toRat| ≤ 1 / (m.toNat + 1) ∧ |(g₁ k - g₂ k).toRat| ≤ 1 / (m.toNat + 1) := by
    exact ⟨ hBa.2 k ( le_trans ( RGFNat.le_max_left _ _ ) ( le_trans ( RGFNat.le_max_left _ _ ) hk ) ), hBd.2 k ( le_trans ( RGFNat.le_max_right _ _ ) ( le_trans ( RGFNat.le_max_left _ _ ) hk ) ), by simpa using RGFRat.isSmall_iff _ _ |>.1 ( hN1 k ( le_trans ( RGFNat.le_max_left _ _ ) ( le_trans ( RGFNat.le_max_right _ _ ) hk ) ) ), by simpa using RGFRat.isSmall_iff _ _ |>.1 ( hN2 k ( le_trans ( RGFNat.le_max_right _ _ ) ( le_trans ( RGFNat.le_max_right _ _ ) hk ) ) ) ⟩;
  simp_all +decide [ abs_le ];
  constructor <;> nlinarith [ inv_pos.mpr ( by positivity : 0 < ( m.toNat : ℚ ) + 1 ), inv_pos.mpr ( by positivity : 0 < ( n.toNat : ℚ ) + 1 ), mul_inv_cancel₀ ( by positivity : ( m.toNat : ℚ ) + 1 ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( n.toNat : ℚ ) + 1 ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( Ba + Bd + 1 : ℚ ) ≠ 0 ) ]

/-! ## Pre-reals -/

/-- RGF generative reals (pre-type): Cauchy sequences of `RGFRat`, indexed by `RGFNat`. -/
structure PreReal where
  approx : RGFNat → RGFRat
  cauchy : IsRGFCauchy approx

namespace PreReal

def Equiv (a b : PreReal) : Prop := SeqEquiv a.approx b.approx

theorem equiv_refl (a : PreReal) : a.Equiv a := SeqEquiv.refl a.approx

theorem equiv_symm {a b : PreReal} (h : a.Equiv b) : b.Equiv a := SeqEquiv.symm h

theorem equiv_trans {a b c : PreReal} (h1 : a.Equiv b) (h2 : b.Equiv c) : a.Equiv c :=
  SeqEquiv.trans h1 h2

instance preRealSetoid : Setoid PreReal where
  r := Equiv
  iseqv := ⟨equiv_refl, fun h => equiv_symm h, fun h1 h2 => equiv_trans h1 h2⟩

end PreReal

/-- RGF reals: the quotient type of equivalence classes of `PreReal`.
    The Cauchy sequences are indexed by `RGFNat` (not the built-in `ℕ`). -/
def RGFReal' := Quotient PreReal.preRealSetoid

namespace RGFReal'

def ofRGFRat (q : RGFRat) : RGFReal' :=
  Quotient.mk _ ⟨fun _ => q, IsRGFCauchy.const q⟩

def zero : RGFReal' := ofRGFRat RGFRat.zero
def one : RGFReal' := ofRGFRat RGFRat.one

def add : RGFReal' → RGFReal' → RGFReal' :=
  Quotient.lift₂
    (fun x y => Quotient.mk _ ⟨fun n => x.approx n + y.approx n, x.cauchy.add y.cauchy⟩)
    (fun _ _ _ _ h1 h2 => Quotient.sound (SeqEquiv.add h1 h2))

def neg : RGFReal' → RGFReal' :=
  Quotient.lift
    (fun x => Quotient.mk _ ⟨fun n => RGFRat.neg (x.approx n), x.cauchy.neg⟩)
    (fun _ _ h => Quotient.sound (SeqEquiv.neg h))

def mul : RGFReal' → RGFReal' → RGFReal' :=
  Quotient.lift₂
    (fun x y => Quotient.mk _ ⟨fun n => x.approx n * y.approx n, x.cauchy.mul y.cauchy⟩)
    (fun a₁ _b₁ _a₂ b₂ h1 h2 =>
      Quotient.sound (SeqEquiv.mul a₁.cauchy b₂.cauchy h1 h2))

instance : Zero RGFReal' where zero := zero
instance : One RGFReal' where one := one
instance : Add RGFReal' where add := add
instance : Neg RGFReal' where neg := neg
instance : Mul RGFReal' where mul := mul
instance : Sub RGFReal' where sub a b := a + neg b

/-! ## Embedding chain of the number-system hierarchy -/

def embedNatInt : RGFNat → RGFInt := RGFInt.ofRGFNat
def embedIntRat : RGFInt → RGFRat := RGFRat.ofRGFInt
def embedRatReal : RGFRat → RGFReal' := RGFReal'.ofRGFRat
def embedNatReal : RGFNat → RGFReal' := embedRatReal ∘ embedIntRat ∘ embedNatInt

end RGFReal'
end RGF