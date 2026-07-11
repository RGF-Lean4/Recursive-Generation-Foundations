/-
  RGF/Physics/Dynamics/FaultToleranceThreshold.lean
  (module `RGF.Physics.Dynamics.FaultToleranceThreshold`)

  **Direction 5.2 — math-layer kernel of the fault-tolerance threshold theorem.**

  The general fault-tolerance threshold theorem (below a critical noise rate the
  encoded logical information is protected as the code distance grows, for arbitrary
  topological / stabilizer codes) is a large research effort resting on
  statistical-mechanics / percolation estimates absent from Mathlib.  What *is*
  clean, faithful, and fully provable is the threshold theorem for the **simplest
  stabilizer code** — the distance-`(2m+1)` repetition code with independent
  bit-flip noise of rate `p` and majority-vote decoding — whose threshold is exactly
  `p_c = 1/2`.

  This file proves that kernel:

    * `failProb m p`            the logical failure probability of the distance
                               `2m+1` repetition code: the probability of `> m`
                               independent errors (majority vote then fails);
    * `failProb_le`            the **sub-threshold exponential suppression bound**
                               `failProb m p ≤ 2·p·(4·p·(1−p))^m`;
    * `four_pq_lt_one`         `4·p·(1−p) < 1` exactly when `p ≠ 1/2`;
    * `threshold_theorem`      **below threshold** (`0 ≤ p < 1/2`) the logical
                               failure probability tends to `0` as the code
                               distance grows (`m → ∞`) — topological order is
                               robust; the protection improves exponentially with
                               distance.

  This is the rigorous mathematical core of "fault-tolerance threshold (topological order is robust when noise < critical rate)"
  for the simplest code; the general-code / percolation content is documented as
  out-of-scope research engineering.
-/
import Mathlib

open Filter Topology Finset

namespace RGF
namespace Physics
namespace FaultTolerance

/-- Logical failure probability of the distance-`(2m+1)` repetition code under
independent bit-flip noise of rate `p` with majority-vote decoding: the probability
that strictly more than `m` of the `2m+1` physical bits are flipped. -/
noncomputable def failProb (m : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (m + 1) (2 * m + 1),
    (Nat.choose (2 * m + 1) k : ℝ) * p ^ k * (1 - p) ^ (2 * m + 1 - k)

/-
`failProb` is nonnegative for a genuine probability `0 ≤ p ≤ 1`.
-/
theorem failProb_nonneg {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ failProb m p := by
  exact Finset.sum_nonneg fun _ _ => mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp0 _ ) ) ( pow_nonneg ( sub_nonneg.2 hp1 ) _ )

/-
**Sub-threshold exponential suppression bound.**  For `0 ≤ p ≤ 1/2` the failure
probability is bounded by `2·p·(4·p·(1−p))^m`.  (Each failing term `p^k (1−p)^{n−k}`
with `k ≥ m+1` is `≤ p^{m+1}(1−p)^m` since `p ≤ 1−p`, and there are at most `2^{2m+1}`
such terms.)
-/
theorem failProb_le {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    failProb m p ≤ 2 * p * (4 * p * (1 - p)) ^ m := by
  -- Let $q = 1 - p$. Note $0 \leq p \leq 1/2 \leq q$, so $p \leq q$.
  set q : ℝ := 1 - p
  have hpq : p ≤ q := by
    exact le_tsub_of_add_le_left <| by linarith;
  have h_pmqm_factor : (∑ k ∈ Finset.Icc (m + 1) (2 * m + 1), (Nat.choose (2 * m + 1) k : ℝ) * p ^ k * q ^ (2 * m + 1 - k)) ≤ (∑ k ∈ Finset.Icc (m + 1) (2 * m + 1), (Nat.choose (2 * m + 1) k : ℝ)) * (p ^ (m + 1) * q ^ m) := by
    -- For each $k$ in the range $m+1$ to $2m+1$, we have $p^k q^{2m+1-k} \leq p^{m+1} q^m$.
    have h_term_bound : ∀ k ∈ Finset.Icc (m + 1) (2 * m + 1), p ^ k * q ^ (2 * m + 1 - k) ≤ p ^ (m + 1) * q ^ m := by
      intro k hk; rw [ show 2 * m + 1 - k = m - ( k - ( m + 1 ) ) by { rw [ Nat.sub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( show m + 1 ≤ k from Finset.mem_Icc.mp hk |>.1 ), Nat.sub_add_cancel ( show k - ( m + 1 ) ≤ m from by { norm_num at *; omega } ) ] } ] ; ring_nf;
      rw [ show k = m + 1 + ( k - ( m + 1 ) ) by rw [ Nat.add_sub_cancel' ( by linarith [ Finset.mem_Icc.mp hk ] ) ] ] ; ring_nf;
      simp +zetaDelta at *;
      rw [ mul_assoc, show ( 1 - p ) ^ m = ( 1 - p ) ^ ( m - ( k - ( 1 + m ) ) ) * ( 1 - p ) ^ ( k - ( 1 + m ) ) by rw [ ← pow_add, Nat.sub_add_cancel ( by omega ) ] ];
      exact mul_le_mul_of_nonneg_left ( by rw [ mul_comm ] ; exact mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by linarith ) ( by linarith ) _ ) ( by exact pow_nonneg ( by linarith ) _ ) ) ( by exact mul_nonneg hp0 ( pow_nonneg hp0 _ ) );
    simpa only [ Finset.sum_mul _ _ _ ] using Finset.sum_le_sum fun x hx => by simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left ( h_term_bound x hx ) ( Nat.cast_nonneg _ ) ;
  -- The sum of binomial coefficients $\sum_{k=m+1}^{2m+1} \binom{2m+1}{k}$ is at most $2^{2m+1}$.
  have h_sum_choose : (∑ k ∈ Finset.Icc (m + 1) (2 * m + 1), (Nat.choose (2 * m + 1) k : ℝ)) ≤ 2 ^ (2 * m + 1) := by
    rw_mod_cast [ ← Nat.sum_range_choose ];
    exact Finset.sum_le_sum_of_subset ( fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp hx ] ) );
  convert h_pmqm_factor.trans ( mul_le_mul_of_nonneg_right h_sum_choose <| by exact mul_nonneg ( pow_nonneg hp0 _ ) <| pow_nonneg ( sub_nonneg.2 <| by linarith ) _ ) using 1 ; ring;
  norm_num [ pow_mul' ]

/-- `4·p·(1−p) < 1` precisely when `p ≠ 1/2` (with equality at `p = 1/2`). -/
theorem four_pq_lt_one {p : ℝ} (hp : p ≠ 1 / 2) : 4 * p * (1 - p) < 1 := by
  have h : 2 * p - 1 ≠ 0 := fun h => hp (by linarith)
  have hpos : 0 < (2 * p - 1) ^ 2 := by positivity
  nlinarith [hpos]

/-
**Fault-tolerance threshold theorem (repetition code).**  Below the threshold
`p_c = 1/2`, the logical failure probability of the repetition code tends to `0` as
the code distance grows: `p < 1/2 ⇒ failProb m p → 0` as `m → ∞`.  Encoded
information is protected (topological order is robust) with exponential suppression
in the code distance.
-/
theorem threshold_theorem {p : ℝ} (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
    Tendsto (fun m => failProb m p) atTop (𝓝 0) := by
  refine' squeeze_zero ( fun m => failProb_nonneg hp0 ( by linarith ) ) ( fun m => failProb_le hp0 ( by linarith ) ) _;
  simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by nlinarith ) ( by nlinarith : 4 * p * ( 1 - p ) < 1 ) )

end FaultTolerance
end Physics
end RGF