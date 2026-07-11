/-
  RGF/ConstructiveFeynmanKac.lean

  Direction III — Constructive path integral and the discrete Feynman–Kac
  formula on lattice dynamics.

  A completely explicit, `sorry`-free development building the rigorous bridge
  between parabolic (diffusive, statistical) evolution and the sum-over-paths
  (path-integral) representation, and its Wick rotation to the complex/quantum
  amplitude.  Everything is done at the level of the discrete transfer operator
  over an *arbitrary commutative ring* `R`, so that the *same* theorem
  specializes to:
    * `R = ℝ`  — the statistical / heat-semigroup sum over trajectories;
    * `R = ℂ`  — the quantum / Feynman path-integral amplitude.

  Contents:
  * `matPow` : the `n`-step transfer operator (propagator) of a kernel `M`.
  * `pathWeight` : the multiplicative weight `∏ M(p i, p (i+1))` of a discrete
    trajectory `p`.
  * `matPow_eq_path_sum` : the **discrete Feynman–Kac / path-integral formula**
    — the propagator is the sum of trajectory weights over all paths joining the
    endpoints.
  * `matPow_chapman_kolmogorov` : the semigroup (Chapman–Kolmogorov) law — path
    integrals glue by concatenation.
  * `matPow_ringHom` : the **Wick-rotation / complexification bridge** — a ring
    homomorphism (e.g. `ℝ ↪ ℂ`) intertwines the real and complex propagators;
    the analytic continuation `t ↦ i t` is realized algebraically at the level
    of the kernel.
  * `pathWeight_feynmanKac` : the discrete Feynman–Kac factorization of the path
    weight when a potential is attached to the vertices.
-/

import Mathlib

open Finset BigOperators

namespace RGF.FeynmanKac

variable {S : Type*} [Fintype S] [DecidableEq S]
variable {R : Type*} [CommRing R]

/-! ## 1. The transfer operator (propagator) -/

/-- The `n`-step transfer operator (propagator) of a kernel `M : S → S → R`.
    `matPow M 0` is the identity kernel and
    `matPow M (n+1) x y = ∑ z, matPow M n x z * M z y`. -/
def matPow (M : S → S → R) : ℕ → S → S → R
  | 0 => fun x y => if x = y then 1 else 0
  | (n+1) => fun x y => ∑ z : S, matPow M n x z * M z y

@[simp] theorem matPow_zero (M : S → S → R) (x y : S) :
    matPow M 0 x y = if x = y then 1 else 0 := rfl

theorem matPow_succ (M : S → S → R) (n : ℕ) (x y : S) :
    matPow M (n+1) x y = ∑ z : S, matPow M n x z * M z y := rfl

/-- The one-step propagator is the kernel itself. -/
theorem matPow_one (M : S → S → R) (x y : S) : matPow M 1 x y = M x y := by
  simp [matPow_succ, matPow_zero]

/-! ## 2. Path weights and the path-integral formula -/

/-- The multiplicative weight of a discrete trajectory `p : Fin (n+1) → S`:
    the product of the kernel over the `n` consecutive edges. -/
def pathWeight (M : S → S → R) {n : ℕ} (p : Fin (n+1) → S) : R :=
  ∏ i : Fin n, M (p i.castSucc) (p i.succ)

omit [Fintype S] [DecidableEq S] in
@[simp] theorem pathWeight_zero (M : S → S → R) (p : Fin 1 → S) :
    pathWeight M p = 1 := by
  simp [pathWeight]

/-
**Chapman–Kolmogorov / semigroup law.** Propagating for `m + n` steps equals
    propagating `m` steps, summing over the intermediate state, then propagating
    `n` steps: path integrals glue by concatenation at the midpoint.
-/
theorem matPow_chapman_kolmogorov (M : S → S → R) (m n : ℕ) (x y : S) :
    matPow M (m + n) x y = ∑ z : S, matPow M m x z * matPow M n z y := by
  induction' n with n ih generalizing x y;
  · simp +decide [ matPow_zero ];
  · simp +decide only [← add_assoc, matPow_succ];
    simp +decide only [ih, sum_mul, Finset.mul_sum _ _ _];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

/-
**Discrete Feynman–Kac / path-integral formula.** The `n`-step propagator is
    the sum, over all discrete trajectories `p` joining `x` to `y` in `n` steps,
    of the trajectory weight `∏ M(p i, p(i+1))`.
-/
theorem matPow_eq_path_sum (M : S → S → R) (n : ℕ) (x y : S) :
    matPow M n x y =
      ∑ p : Fin (n+1) → S, (if p 0 = x ∧ p (Fin.last n) = y then pathWeight M p else 0) := by
  induction' n with n ih generalizing x y;
  · rw [ Finset.sum_eq_single ( fun _ => x ) ] <;> simp +decide [ pathWeight ];
    exact fun b hb hx hy => False.elim <| hb <| funext fun i => by fin_cases i; exact hx;
  · -- By the induction hypothesis, we can rewrite the inner sum.
    have h_inner : ∑ z : S, (∑ q : Fin (n + 1) → S, if q 0 = x ∧ q (Fin.last n) = z then pathWeight M q else 0) * M z y = ∑ q : Fin (n + 1) → S, if q 0 = x then pathWeight M q * M (q (Fin.last n)) y else 0 := by
      simp +decide only [sum_mul _ _ _];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    convert h_inner using 1;
    · simp +decide [ ← ih, matPow_succ ];
    · rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun q : Fin ( n + 1 ) → S => Fin.snoc q y ) Finset.univ ) ) ];
      · rw [ Finset.sum_image ] <;> simp +decide [ Fin.snoc ];
        · simp +decide [ pathWeight, Fin.prod_univ_castSucc ];
          simp +decide [ Fin.snoc ];
          congr! 3;
        · exact fun q q' h => by ext i; replace h := congr_fun h ( Fin.castSucc i ) ; aesop;
      · intro p hp hpxy; contrapose! hpxy; simp_all +decide ;
        use fun i => p i.castSucc;
        ext i; induction i using Fin.lastCases <;> simp +decide [ * ] ;

/-! ## 3. Wick rotation / complexification bridge -/

/-
**Wick-rotation / complexification bridge.** Any ring homomorphism
    `f : R →+* R'` (for example the embedding `ℝ ↪ ℂ`, i.e. the analytic
    continuation that turns the real heat propagator into the complex quantum
    amplitude) intertwines the propagators: it maps the statistical propagator of
    a kernel to the quantum propagator of the transported kernel.  Together with
    `matPow_eq_path_sum` this shows the statistical and quantum path integrals
    are the *same* combinatorial object, related by analytic continuation.
-/
theorem matPow_ringHom {R' : Type*} [CommRing R'] (f : R →+* R')
    (M : S → S → R) (n : ℕ) (x y : S) :
    f (matPow M n x y) = matPow (fun a b => f (M a b)) n x y := by
  induction' n with n ih generalizing x y;
  · unfold matPow; aesop;
  · simp +decide [ *, matPow_succ ]

/-! ## 4. Discrete Feynman–Kac with a potential -/

/-
**Feynman–Kac factorization.** If the kernel is a base transition weight `P`
    multiplied by a potential factor `g` attached to the target vertex,
    `M x y = P x y * g y`, then the trajectory weight factorizes into the base
    path weight times the accumulated potential `∏ g` along the trajectory
    (excluding the start point).  This is the discrete Feynman–Kac formula:
    diffusion weight × `exp(−∑ V)` accumulated along the path.
-/
omit [Fintype S] [DecidableEq S] in
theorem pathWeight_feynmanKac (P : S → S → R) (g : S → R) {n : ℕ}
    (p : Fin (n+1) → S) :
    pathWeight (fun x y => P x y * g y) p
      = pathWeight P p * ∏ i : Fin n, g (p i.succ) := by
  simp +decide [ pathWeight, Finset.prod_mul_distrib ]

end RGF.FeynmanKac