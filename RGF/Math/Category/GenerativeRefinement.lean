/-
  RequestProject/GenerativeRefinement.lean

  Original Mathematics II — generative-process refinement (a continent invisible
  to classical point-real numbers).

  Classical real analysis: a real number is a point; a process is a temporary
  ladder to a value.  RGF: every number is produced by an explicit generative
  process.  An isomorphism can move the value, but cannot move the *convergence
  rate* of the process.

  New structure:
    * `GenReal` : a generative process (a rational Cauchy sequence by generation
      scale);
    * `value`   : the forgetful map `GenReal → ℝ` (limit only);
    * `IsModulus` / `Rapid` : a convergence modulus / rapidity — a property of the
      *process*, not of the *value*.

  Core theorems:
    1. Rapid normal form: every real is the value of a rapid process
       (`exists_rapid_value`).
    2. Rapidity is irreducible (the core): two processes with the *same value*,
       one rapid, one not (`rapid_distinguishes_equal_value`).  Rapidity is real
       generative data that does *not* descend along the forgetful map `value`.
    3. Rapid uniqueness: any two rapid processes for the same value are pinned
       within `3/(n+1)` at every index (`rapid_pointwise_rigid`).
-/
import Mathlib

namespace RGF.GenRefine

/-- A generative process: a rational sequence with a proof it is Cauchy. -/
structure GenReal where
  approx : ℕ → ℚ
  isCau : IsCauSeq abs approx

/-- The forgetful map to the classical reals: the limit of the process. -/
noncomputable def value (a : GenReal) : ℝ := Real.mk ⟨a.approx, a.isCau⟩

/-- `m` is a convergence modulus for the process: from index `m k` on, terms are
    within `1/(k+1)`. -/
def IsModulus (a : GenReal) (m : ℕ → ℕ) : Prop :=
  ∀ k p q, m k ≤ p → m k ≤ q → |a.approx p - a.approx q| ≤ 1 / (k + 1)

/-- A process is *rapid* when its own index is a convergence modulus
    (`m = id`). -/
def Rapid (a : GenReal) : Prop :=
  ∀ k p q, k ≤ p → k ≤ q → |a.approx p - a.approx q| ≤ 1 / (k + 1)

theorem rapid_iff_modulus_id (a : GenReal) : Rapid a ↔ IsModulus a id := Iff.rfl

/-! ### A helper: a rationally convergent process is Cauchy -/

theorem isCau_of_tendsto (g : ℕ → ℚ) (L : ℝ)
    (h : Filter.Tendsto (fun n => ((g n : ℚ) : ℝ)) Filter.atTop (nhds L)) :
    IsCauSeq abs g := by
  intro ε hε;
  have := Metric.cauchySeq_iff.1 ( h.cauchySeq );
  obtain ⟨ N, hN ⟩ := this ε ( mod_cast hε ) ; use N; intros j hj; specialize hN j hj N le_rfl; erw [ Real.dist_eq ] at hN; norm_cast at *;

/-! ### A rapid process is uniformly close to its value -/

/--
The value of a rapid process is within `1/(n+1)` of every term.
-/
theorem value_dist_le (a : GenReal) (h : Rapid a) (n : ℕ) :
    |(a.approx n : ℝ) - value a| ≤ 1 / (n + 1) := by
  -- Apply `Real.mk_near_of_forall_near` with x = (a.approx n : ℝ) and ε = 1/(n+1): we need ∃ i, ∀ j ≥ i, |↑(a.approx j) - ↑(a.approx n)| ≤ 1/(n+1).
  have h_near : ∃ i : ℕ, ∀ j ≥ i, |(a.approx j : ℝ) - (a.approx n : ℝ)| ≤ 1 / (n + 1) := by
    use n;
    intro j hj; specialize h n j n; norm_cast at *;
    convert h hj le_rfl using 1 ; norm_num [ Rat.divInt_eq_div ];
    rw [ inv_eq_one_div, le_div_iff₀ ] <;> norm_cast ; norm_num;
    · rw [ inv_eq_one_div, le_div_iff₀ ] ; linarith;
    · linarith;
  rw [ abs_sub_comm, value ];
  apply_rules [ Real.mk_near_of_forall_near ]

/-! ### 1. Rapid normal form -/

/--
Every real number is the value of a rapid generative process.
-/
theorem exists_rapid_value (x : ℝ) : ∃ a : GenReal, Rapid a ∧ value a = x := by
  by_contra h_contra;
  -- By definition of `GenReal`, we can construct such a sequence.
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℚ, (∀ n, |(a n : ℝ) - x| < 1 / (2 * (n + 1))) ∧ (∀ k p q, k ≤ p → k ≤ q → |(a p : ℝ) - (a q : ℝ)| ≤ 1 / (k + 1)) := by
    have h_seq : ∃ (a : ℕ → ℚ), (∀ n, |(a n : ℝ) - x| < 1 / (2 * (n + 1))) := by
      exact ⟨ fun n => Classical.choose ( exists_rat_btwn ( show x - 1 / ( 2 * ( n + 1 ) ) < x by simp +decide ; positivity ) ), fun n => by have := Classical.choose_spec ( exists_rat_btwn ( show x - 1 / ( 2 * ( n + 1 ) ) < x by simp +decide ; positivity ) ) ; exact abs_lt.mpr ⟨ by linarith, by linarith ⟩ ⟩;
    obtain ⟨ a, ha ⟩ := h_seq; use a; refine' ⟨ ha, fun k p q hp hq => _ ⟩ ; rw [ abs_sub_le_iff ] ; constructor <;> norm_num at *;
    · have := ha p; have := ha q; rw [ abs_lt ] at *; nlinarith [ inv_pos.mpr ( by linarith : 0 < ( k : ℝ ) + 1 ), inv_pos.mpr ( by linarith : 0 < ( p : ℝ ) + 1 ), inv_pos.mpr ( by linarith : 0 < ( q : ℝ ) + 1 ), mul_inv_cancel₀ ( by linarith : ( k : ℝ ) + 1 ≠ 0 ), mul_inv_cancel₀ ( by linarith : ( p : ℝ ) + 1 ≠ 0 ), mul_inv_cancel₀ ( by linarith : ( q : ℝ ) + 1 ≠ 0 ), show ( p : ℝ ) ≥ k by norm_cast, show ( q : ℝ ) ≥ k by norm_cast ] ;
    · have := ha p; have := ha q; rw [ abs_lt ] at *; nlinarith [ inv_pos.mpr ( by linarith : 0 < ( k : ℝ ) + 1 ), inv_pos.mpr ( by linarith : 0 < ( p : ℝ ) + 1 ), inv_pos.mpr ( by linarith : 0 < ( q : ℝ ) + 1 ), mul_inv_cancel₀ ( by linarith : ( k : ℝ ) + 1 ≠ 0 ), mul_inv_cancel₀ ( by linarith : ( p : ℝ ) + 1 ≠ 0 ), mul_inv_cancel₀ ( by linarith : ( q : ℝ ) + 1 ≠ 0 ), show ( k : ℝ ) ≤ p by norm_cast, show ( k : ℝ ) ≤ q by norm_cast ] ;
  -- Define the generative process `a` with the given properties.
  obtain ⟨a_gen, ha_gen⟩ : ∃ a_gen : GenReal, a_gen.approx = a ∧ Rapid a_gen := by
    refine' ⟨ ⟨ a, _ ⟩, rfl, _ ⟩;
    convert isCau_of_tendsto a x _;
    exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => le_of_lt <| ha.1 n ) <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_mono ( fun n => by linarith ) tendsto_natCast_atTop_atTop;
    intro k p q hp hq; specialize ha; have := ha.2 k p q hp hq; norm_cast at *;
    rw [ le_div_iff₀ ] at * <;> norm_cast at * ; aesop;
    linarith;
  refine' h_contra ⟨ a_gen, ha_gen.2, _ ⟩;
  have h_value : Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop (nhds x) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => le_of_lt <| ha.1 n ) <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_mono ( fun n => by linarith ) tendsto_natCast_atTop_atTop;
  refine' tendsto_nhds_unique _ h_value;
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε; filter_upwards [ Filter.eventually_ge_atTop ⌈ε⁻¹⌉₊ ] with n hn; have := value_dist_le a_gen ( by aesop ) n; simp_all +decide [ dist_eq_norm ] ;
  exact this.trans_lt ( inv_lt_of_inv_lt₀ hε ( by linarith ) )

/-! ### 2. Rapidity is irreducible -/

/--
There exist two processes with the *same value* (here `0`), one rapid and one
    not: rapidity is genuine generative data not visible through `value`.
-/
theorem rapid_distinguishes_equal_value :
    ∃ a b : GenReal, value a = value b ∧ Rapid a ∧ ¬ Rapid b := by
  -- Consider the following two processes:
  use ⟨fun n => 0, by
    exact fun ε hε => ⟨ 0, fun n hn => by simpa using hε ⟩⟩, ⟨fun n => if n = 0 then 2 else 0, by
    exact fun ε hε => ⟨ 1, fun n hn => by aesop ⟩ ;⟩
  generalize_proofs at *;
  unfold value Rapid; norm_num;
  refine' ⟨ _, _, 0, 0, _, 1, _, _ ⟩ <;> norm_num;
  · refine' Real.mk_eq.mpr _;
    intro ε hε; use 1; intros n hn; aesop;
  · exact fun _ _ _ _ _ => by positivity;

/-! ### 3. Rapid uniqueness -/

/--
Two rapid processes for the same value are pinned within `3/(n+1)` at every
    index.
-/
theorem rapid_pointwise_rigid (a b : GenReal) (ha : Rapid a) (hb : Rapid b)
    (hval : value a = value b) (n : ℕ) :
    |(a.approx n : ℝ) - (b.approx n : ℝ)| ≤ 3 / (n + 1) := by
  -- Use `value_dist_le a ha n` : |↑(a.approx n) - value a| ≤ 1/(n+1) and `value_dist_le b hb n` : |↑(b.approx n) - value b| ≤ 1/(n+1).
  have h1 := value_dist_le a ha n
  have h2 := value_dist_le b hb n
  rw [hval] at h1;
  grind

end RGF.GenRefine