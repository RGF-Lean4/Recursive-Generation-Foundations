/-
  Paper 1 — "Law as the inevitable emergence of change: the physical foundations of Recursive Constitutive Dynamics"
  (Law as the necessary emergence of change: the physical foundations of
  Recursive Constitutive Dynamics), L. Sun 2026.

  Placed in the RGF **Generative** layer (Layer 1 / Generative spine).

  Formalizes cleanly-statable cores of the Recursive Constitutive Equation
  (RCE)  `Ψ_{n+1} = R[Ψ_n] + ξ_n`, whose constitutive map `R` and intrinsic
  noise `ξ` are two faces of the same generative dynamics:

  * with vanishing intrinsic noise the RCE is exactly the iterated constitutive
    map `R^[n]` (the deterministic backbone of the recursion);
  * **self-referential closure (P5)**: an `R`-invariant subset is closed under
    the whole forward orbit — a surviving fragment carries a self-map that keeps
    its states inside the fragment for all times;
  * **locking survival as a self-consistent fixed point**: a uniformly
    contracting constitutive map on a nonempty complete metric space has a
    *unique* fixed point, i.e. the surviving self-referential closure is unique.
-/
import Mathlib

namespace RGF.Paper1

/-- RCE with zero intrinsic noise is the iterated constitutive map: the
`(n+1)`-step evolution applies `R` to the `n`-step evolution. -/
theorem rce_zero_noise_iterate {α : Type*} (R : α → α) (n : ℕ) (Ψ : α) :
    R^[n + 1] Ψ = R (R^[n] Ψ) :=
  Function.iterate_succ_apply' R n Ψ

/-- Self-referential closure (P5): if a subset `S` is invariant under the
constitutive map `R` (`∀ x ∈ S, R x ∈ S`), then every orbit that starts in `S`
stays in `S` for all times. -/
theorem invariant_iterate_mem {α : Type*} (R : α → α) (S : Set α)
    (hS : ∀ x ∈ S, R x ∈ S) (x : α) (hx : x ∈ S) (n : ℕ) :
    R^[n] x ∈ S :=
  Nat.recOn n hx fun n ih => by
    rw [Function.iterate_succ_apply']; exact hS _ ih

/-- Locking survival as a unique self-consistent fixed point: a uniformly
contracting constitutive map on a nonempty complete metric space has a unique
fixed point (the surviving self-referential closure is unique). -/
theorem contraction_unique_fixedPoint {α : Type*} [MetricSpace α]
    [CompleteSpace α] [Nonempty α] {K : NNReal} {R : α → α}
    (h : ContractingWith K R) :
    ∃! x, R x = x := by
  have h_fixed_point : ∃ x, R x = x := by
    have := h.exists_fixedPoint (Classical.arbitrary α)
    exact Exists.imp (fun x => And.left) (this (edist_ne_top _ _))
  obtain ⟨x, hx⟩ := h_fixed_point
  refine ⟨x, hx, fun y hy => ?_⟩
  have hlip := h.dist_le_mul x y
  simp only [hx, hy] at hlip
  refine (dist_le_zero.mp ?_).symm
  nlinarith [show (K : ℝ) < 1 from h.1, show (0 : ℝ) ≤ dist x y from dist_nonneg]

end RGF.Paper1
