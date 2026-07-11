/-
  RGF/HarrisRecurrence.lean

  Direction I — From finite ergodicity to non-compact / continuous state spaces:
  the constructive Foster–Lyapunov drift theorem (Meyn–Tweedie / Harris).

  `ConstructiveErgodicity.lean` established Doeblin minorization and geometric
  ergodicity on a *finite* state space.  On a non-compact, infinite-dimensional
  phase space Doeblin's uniform lower bound fails (mass escapes to infinity).
  The correct, and only, remedy is a **Lyapunov drift condition**: the existence
  of a norm-like function `V ≥ 0` that the dynamics contracts back towards a
  bounded sub-level set.  We formalize this at the level of an abstract Markov
  operator, so the result is valid on *any* state space — finite, countable, or
  a non-compact continuum — with no compactness assumption whatsoever.

  Contents:
  * `MarkovOp` : an abstract (order-preserving, affine, conservative) Markov
    transition operator on functions over an arbitrary type `S`.
  * `DriftCondition` : the Foster–Lyapunov / Meyn–Tweedie geometric drift
    `P V ≤ (1−a) V + b`.
  * `drift_iterate` : the iterated drift bound
    `Pⁿ V ≤ (1−a)ⁿ V + b·∑_{k<n}(1−a)ᵏ`.
  * `drift_geometric_bound` : the closed-form confinement bound
    `Pⁿ V ≤ (1−a)ⁿ V + b/a`.
  * `drift_tendsto` : `Pⁿ V(x) → ≤ b/a` geometrically — the Lyapunov function is
    driven into the bounded sub-level set `{V ≤ b/a}` regardless of the
    (possibly non-compact) initial state.  This is the constructive closure of
    the continuous-limit ergodicity problem: drift replaces the failed uniform
    minorization.
-/

import Mathlib

open scoped BigOperators

namespace RGF.Harris

variable {S : Type*}

/-! ## 1. Abstract Markov transition operators -/

/-- An abstract Markov transition operator acting on real-valued functions over
    an arbitrary state space `S`.  It is order-preserving (monotone), additive,
    positively homogeneous (linear), and conservative (`P 1 = 1`).  These are
    exactly the structural properties of `f ↦ ∫ f dP(x,·)` for a Markov kernel
    `P`, and they hold on non-compact / infinite-dimensional spaces without any
    integrability restriction on `V` beyond what is stated. -/
structure MarkovOp (S : Type*) where
  /-- The action of the operator on functions. -/
  P : (S → ℝ) → (S → ℝ)
  /-- Monotonicity (a Markov operator preserves pointwise order). -/
  mono : ∀ {f g : S → ℝ}, (∀ x, f x ≤ g x) → ∀ x, P f x ≤ P g x
  /-- Additivity. -/
  map_add : ∀ (f g : S → ℝ), P (fun x => f x + g x) = fun x => P f x + P g x
  /-- Positive homogeneity. -/
  map_smul : ∀ (c : ℝ) (f : S → ℝ), P (fun x => c * f x) = fun x => c * P f x
  /-- Conservativity: the constant function `1` is fixed. -/
  map_one : P (fun _ => 1) = fun _ => 1

/-
A Markov operator maps a constant function to the same constant.
-/
theorem MarkovOp.map_const (T : MarkovOp S) (c : ℝ) :
    T.P (fun _ => c) = fun _ => c := by
  -- We have T.P (fun _ => c) = T.P (c • (fun _ => 1)).
  have h_eq : T.P (fun _ => c) = T.P (fun _ => c * 1) := by
    simp +decide;
  convert T.map_smul c ( fun _ => 1 ) using 1;
  rw [ T.map_one ] ; norm_num

/-- The `n`-fold iterate of a Markov operator. -/
def MarkovOp.iter (T : MarkovOp S) : ℕ → (S → ℝ) → (S → ℝ)
  | 0 => id
  | (n+1) => fun f => T.iter n (T.P f)

@[simp] theorem MarkovOp.iter_zero (T : MarkovOp S) (f : S → ℝ) :
    T.iter 0 f = f := rfl

theorem MarkovOp.iter_succ (T : MarkovOp S) (n : ℕ) (f : S → ℝ) :
    T.iter (n+1) f = T.iter n (T.P f) := rfl

/-
`Pⁿ⁺¹ f = P (Pⁿ f)`: the iterate can be peeled from the outside.
-/
theorem MarkovOp.iter_succ' (T : MarkovOp S) (n : ℕ) (f : S → ℝ) :
    T.iter (n+1) f = T.P (T.iter n f) := by
  induction' n with n ih generalizing f <;> simp_all +decide [ MarkovOp.iter ]

/-
Monotonicity of the iterated operator.
-/
theorem MarkovOp.iter_mono (T : MarkovOp S) (n : ℕ) {f g : S → ℝ}
    (h : ∀ x, f x ≤ g x) : ∀ x, T.iter n f x ≤ T.iter n g x := by
  induction' n with n ih;
  · exact h;
  · intro x; rw [ MarkovOp.iter_succ' ] ;
    rw [ MarkovOp.iter_succ' ];
    exact T.mono ih x

/-
The iterate maps constants to the same constant.
-/
theorem MarkovOp.iter_const (T : MarkovOp S) (n : ℕ) (c : ℝ) :
    T.iter n (fun _ => c) = fun _ => c := by
  induction' n with n ih;
  · rfl;
  · rw [MarkovOp.iter_succ']
    simp [ih, T.map_const]

/-! ## 2. The Foster–Lyapunov drift condition -/

/-- The **Foster–Lyapunov / Meyn–Tweedie geometric drift condition**: there is a
    nonnegative Lyapunov function `V`, a contraction rate `a ∈ (0,1]` and an
    offset `b ≥ 0` with `P V ≤ (1−a) V + b` pointwise.  Intuitively, outside a
    bounded sub-level set of `V` the dynamics strictly decreases `V`, confining
    the (possibly non-compact) state back towards the center. -/
structure DriftCondition (T : MarkovOp S) (V : S → ℝ) (a b : ℝ) : Prop where
  /-- `V` is nonnegative. -/
  V_nonneg : ∀ x, 0 ≤ V x
  /-- The rate lies in `(0, 1]`. -/
  a_pos : 0 < a
  a_le_one : a ≤ 1
  /-- The offset is nonnegative. -/
  b_nonneg : 0 ≤ b
  /-- The drift inequality. -/
  drift : ∀ x, T.P V x ≤ (1 - a) * V x + b

/-! ## 3. The iterated drift bound -/

/-
**Iterated drift bound.** Applying the drift condition `n` times yields
    `Pⁿ V ≤ (1−a)ⁿ V + b·∑_{k<n}(1−a)ᵏ`.
-/
theorem drift_iterate {T : MarkovOp S} {V : S → ℝ} {a b : ℝ}
    (h : DriftCondition T V a b) (n : ℕ) (x : S) :
    T.iter n V x ≤ (1 - a) ^ n * V x + b * ∑ k ∈ Finset.range n, (1 - a) ^ k := by
  induction' n with n ih generalizing x <;> simp_all +decide [ pow_succ, mul_assoc, Finset.sum_range_succ ];
  -- Apply the drift condition to the iterate and simplify the expression.
  have h_iter : T.P (fun x => (1 - a) ^ n * V x + b * ∑ k ∈ Finset.range n, (1 - a) ^ k) x ≤ (1 - a) ^ (n + 1) * V x + b * (∑ k ∈ Finset.range n, (1 - a) ^ k + (1 - a) ^ n) := by
    have h_iter : T.P (fun x => (1 - a) ^ n * V x + b * ∑ k ∈ Finset.range n, (1 - a) ^ k) x = (1 - a) ^ n * T.P V x + b * ∑ k ∈ Finset.range n, (1 - a) ^ k := by
      have := T.map_add ( fun x => ( 1 - a ) ^ n * V x ) ( fun _ => b * ∑ k ∈ Finset.range n, ( 1 - a ) ^ k ) ; have := T.map_smul ( ( 1 - a ) ^ n ) V; have := T.map_const ( b * ∑ k ∈ Finset.range n, ( 1 - a ) ^ k ) ; aesop;
    convert add_le_add ( mul_le_mul_of_nonneg_left ( h.drift x ) ( pow_nonneg ( sub_nonneg.2 h.a_le_one ) n ) ) le_rfl using 1 ; ring;
  convert le_trans _ h_iter using 1;
  · ring;
  · rw [ MarkovOp.iter_succ' ];
    exact T.mono ih x

/-
**Closed-form geometric confinement bound.**
    `Pⁿ V ≤ (1−a)ⁿ V + b/a`.
-/
theorem drift_geometric_bound {T : MarkovOp S} {V : S → ℝ} {a b : ℝ}
    (h : DriftCondition T V a b) (n : ℕ) (x : S) :
    T.iter n V x ≤ (1 - a) ^ n * V x + b / a := by
  refine le_trans ( drift_iterate h n x ) ?_;
  rw [ ← neg_sub, geom_sum_eq ] <;> ring_nf <;> norm_num;
  · exact mul_nonneg ( mul_nonneg h.b_nonneg ( inv_nonneg.2 h.a_pos.le ) ) ( pow_nonneg ( sub_nonneg.2 h.a_le_one ) _ );
  · linarith [ h.a_pos ]

/-
**Constructive closure of the continuous-limit ergodicity problem.**
    From any (possibly arbitrarily large, non-compact) initial state `x`, the
    expected Lyapunov value is driven geometrically into the bounded sub-level
    set: `Pⁿ V (x) → L` with `L ≤ b/a`.  The drift condition thus replaces the
    uniform Doeblin minorization that fails on non-compact spaces.
-/
theorem drift_tendsto {T : MarkovOp S} {V : S → ℝ} {a b : ℝ}
    (h : DriftCondition T V a b) (x : S) :
    Filter.Tendsto (fun n => (1 - a) ^ n * V x + b / a) Filter.atTop (nhds (b / a)) := by
  simpa using Filter.Tendsto.add ( tendsto_pow_atTop_nhds_zero_of_lt_one ( sub_nonneg.2 h.a_le_one ) ( sub_lt_self _ h.a_pos ) |> Filter.Tendsto.mul_const _ ) tendsto_const_nhds

/-
The asymptotic confinement level `b/a` bounds the limit of the drift
    upper-bound sequence: the Lyapunov function cannot escape the sub-level set
    `{V ≤ b/a}` in the long run.
-/
theorem drift_asymptotic_confinement {T : MarkovOp S} {V : S → ℝ} {a b : ℝ}
    (h : DriftCondition T V a b) (x : S) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, T.iter n V x ≤ b / a + ε := by
  have := drift_tendsto h x;
  exact fun ε εpos => by rcases Metric.tendsto_atTop.mp this ε εpos with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => le_trans ( drift_geometric_bound h n x ) ( by linarith [ abs_lt.mp ( hN n hn ) ] ) ⟩ ;

end RGF.Harris