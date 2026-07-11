/-
  Spectral graph theory: Rayleigh quotient and variational characterization
  Spectral Graph Theory: Rayleigh Quotient and Variational Characterization

  This file formalizes:
  - the definition and basic properties of the Rayleigh quotient
  - the Rayleigh quotient of a constant function = 0
  - nonnegativity and upper bound of the Rayleigh quotient
-/

import Mathlib

open Finset BigOperators

/-! ## Definition of the Rayleigh quotient -/

/-- Dirichlet energy E(f) = (1/2) ∑_{v~u} (f(v) - f(u))². -/
noncomputable def SimpleGraph.dirichletERQ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : ℝ :=
  (1 / 2) * ∑ v : V, ∑ u ∈ G.neighborFinset v, (f v - f u) ^ 2

/-- Degree-weighted norm ||f||²_D = ∑_v deg(v) · f(v)². -/
noncomputable def SimpleGraph.degNormSqRQ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : ℝ :=
  ∑ v : V, ((G.neighborFinset v).card : ℝ) * f v ^ 2

/-- Rayleigh quotient R(f) = E(f) / ||f||²_D. -/
noncomputable def SimpleGraph.rayleighQuotientRQ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) : ℝ :=
  if G.degNormSqRQ f = 0 then 0
  else G.dirichletERQ f / G.degNormSqRQ f

/-! ## Basic properties -/

/-- The Dirichlet energy is nonnegative. -/
theorem SimpleGraph.dirichletERQ_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) :
    0 ≤ G.dirichletERQ f := by
  unfold dirichletERQ
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun v _ =>
    Finset.sum_nonneg fun u _ => sq_nonneg _

/-- The degree-weighted norm is nonnegative. -/
theorem SimpleGraph.degNormSqRQ_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) :
    0 ≤ G.degNormSqRQ f := by
  unfold degNormSqRQ
  exact Finset.sum_nonneg fun v _ => mul_nonneg (by positivity) (sq_nonneg _)

/-! ## Constant functions -/

/-- The Dirichlet energy of a constant function is zero. -/
theorem SimpleGraph.dirichletERQ_const {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) :
    G.dirichletERQ (fun _ => c) = 0 := by
  unfold dirichletERQ
  simp [sub_self]

/-- The Rayleigh quotient of a constant function is zero. -/
theorem SimpleGraph.rayleighQuotientRQ_const {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) :
    G.rayleighQuotientRQ (fun _ => c) = 0 := by
  unfold rayleighQuotientRQ
  simp [dirichletERQ_const]

/-! ## Nonnegativity of the Rayleigh quotient -/

/-- The Rayleigh quotient is nonnegative. -/
theorem SimpleGraph.rayleighQuotientRQ_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) :
    0 ≤ G.rayleighQuotientRQ f := by
  unfold rayleighQuotientRQ
  split
  · exact le_refl 0
  · exact div_nonneg (dirichletERQ_nonneg G f) (degNormSqRQ_nonneg G f)

/-! ## Upper bound of the Rayleigh quotient -/

/-
Dirichlet energy ≤ 2 · degree-weighted norm.
-/
theorem SimpleGraph.dirichletERQ_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) :
    G.dirichletERQ f ≤ 2 * G.degNormSqRQ f := by
  -- Applying the inequality $(a - b)^2 \leq 2(a^2 + b^2)$ to each term in the sum.
  have h_ineq : ∀ v u : V, (f v - f u) ^ 2 ≤ 2 * (f v ^ 2 + f u ^ 2) := by
    exact fun v u => by linarith [ sq_nonneg ( f v + f u ) ] ;
  refine' le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun v _ ↦ Finset.sum_le_sum fun u hu ↦ h_ineq v u ) ( by positivity ) ) _;
  simp +decide [ Finset.mul_sum _ _ _, SimpleGraph.degNormSqRQ ];
  simp +decide [ Finset.sum_add_distrib, two_mul, SimpleGraph.degree, SimpleGraph.neighborFinset ];
  simp +decide [ SimpleGraph.neighborSet, Finset.sum_filter ];
  rw [ Finset.sum_comm ];
  simp +decide [ SimpleGraph.adj_comm, Finset.sum_ite ]

/-- The Rayleigh quotient is at most 2. -/
theorem SimpleGraph.rayleighQuotientRQ_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) :
    G.rayleighQuotientRQ f ≤ 2 := by
  unfold rayleighQuotientRQ
  split
  · norm_num
  · next h =>
    rw [div_le_iff₀ (lt_of_le_of_ne (degNormSqRQ_nonneg G f) (Ne.symm h))]
    exact dirichletERQ_le_two G f

/-! ## Non-constant functions -/

/-- Non-constant function. -/
def SimpleGraph.IsNonConstantRQ {V : Type*} [Fintype V]
    (f : V → ℝ) : Prop :=
  ∃ v w : V, f v ≠ f w

/-
The Dirichlet energy of a non-constant function is positive (on a connected graph).
-/
theorem SimpleGraph.dirichletERQ_pos_of_nonconstant {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ)
    (hf : SimpleGraph.IsNonConstantRQ f)
    (hconn : G.Connected) :
    0 < G.dirichletERQ f := by
  -- By definition of $IsNonConstantRQ$, there exist $v$ and $w$ such that $f(v) \neq f(w)$.
  obtain ⟨v, w, hvw⟩ : ∃ v w : V, f v ≠ f w := by
    exact hf;
  -- Since $G$ is connected, there exists a path from $v$ to $w$.
  obtain ⟨p, hp⟩ : ∃ p : G.Walk v w, True := by
    simpa using hconn v w;
  -- Along this path, at least one edge $(a,b)$ has $f(a) \neq f(b)$, contributing $(f(a)-f(b))^2 > 0$ to the Dirichlet energy sum.
  obtain ⟨a, b, hab⟩ : ∃ a b : V, G.Adj a b ∧ f a ≠ f b := by
    induction' p with u v w ih;
    · tauto;
    · grind;
  refine' mul_pos ( by norm_num ) ( lt_of_lt_of_le _ ( Finset.single_le_sum ( fun v _ => Finset.sum_nonneg fun u _ => sq_nonneg ( f v - f u ) ) ( Finset.mem_univ a ) ) );
  exact lt_of_lt_of_le ( by exact sq_pos_of_ne_zero ( sub_ne_zero_of_ne hab.2 ) ) ( Finset.single_le_sum ( fun x _ => sq_nonneg ( f a - f x ) ) ( by aesop ) )
