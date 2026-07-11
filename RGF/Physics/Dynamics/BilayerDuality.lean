/-
  RequestProject/BilayerDuality.lean

  Original Mathematics I — bilayer duality (a universal structural law).

  Setup:
      generate : R → E
      modify   : E → R
      step   := modify ∘ generate : R → R   (rule-layer dynamics)
      costep := generate ∘ modify : E → E   (mirror dynamics — no classical object)

  Theorems:
    1. Fixed-point duality (unconditional): `Fix(step) ≃ Fix(costep)`, a mutually
       inverse bijection, so `|Fix(step)| = |Fix(costep)|`.
    2. Intertwining (semi-conjugacy): `generate ∘ stepⁿ = costepⁿ ∘ generate`
       and `modify ∘ costepⁿ = stepⁿ ∘ modify`.
    3. Recurrence duality (unconditional): for each period `n ≥ 1`, the
       `n`-periodic points biject, `Perₙ(step) ≃ Perₙ(costep)`, with explicit
       inverse `e ↦ step^{n-1}(modify e)`.
    4. Recurrence rigidity (the conjecture, now a theorem): the full sets of
       periodic points biject, `periodicPts(step) ≃ periodicPts(costep)`.
-/
import Mathlib

namespace RGF.Bilayer

variable {R E : Type*}

/-- The rule-layer dynamics `step = modify ∘ generate`. -/
def step (generate : R → E) (modify : E → R) : R → R := modify ∘ generate

/-- The mirror dynamics `costep = generate ∘ modify`. -/
def costep (generate : R → E) (modify : E → R) : E → E := generate ∘ modify

/-! ### 2. Intertwining (semi-conjugacy) -/

/--
`generate` intertwines `step` and `costep`: `generate ∘ stepⁿ = costepⁿ ∘ generate`.
-/
theorem generate_intertwine (generate : R → E) (modify : E → R) (n : ℕ) :
    generate ∘ (step generate modify)^[n] = (costep generate modify)^[n] ∘ generate := by
  induction' n with n ih <;> simp_all +decide [ Function.comp_assoc ];
  convert congr_arg ( fun f => f ∘ step generate modify ) ih using 1

/--
`modify` intertwines `costep` and `step`: `modify ∘ costepⁿ = stepⁿ ∘ modify`.
-/
theorem modify_intertwine (generate : R → E) (modify : E → R) (n : ℕ) :
    modify ∘ (costep generate modify)^[n] = (step generate modify)^[n] ∘ modify := by
  induction' n with n ih <;> simp_all +decide [ step, costep ] ;
  simp +decide only [← Function.comp_assoc, ih]

/--
Pointwise form of `generate`-intertwining.
-/
theorem generate_iterate (generate : R → E) (modify : E → R) (n : ℕ) (r : R) :
    generate ((step generate modify)^[n] r) = (costep generate modify)^[n] (generate r) := by
  exact congr_fun ( generate_intertwine generate modify n ) r

/-! ### 1. Fixed-point duality -/

/--
A fixed point of `step` generates a fixed point of `costep`.
-/
theorem generate_fixed_of_fixed (generate : R → E) (modify : E → R) {r : R}
    (h : step generate modify r = r) :
    costep generate modify (generate r) = generate r := by
  unfold step costep at *; aesop;

/--
A fixed point of `costep` is modified to a fixed point of `step`.
-/
theorem modify_fixed_of_fixed (generate : R → E) (modify : E → R) {e : E}
    (h : costep generate modify e = e) :
    step generate modify (modify e) = modify e := by
  simp_all +decide [ step, costep, Function.comp ]

/--
Fixed-point duality: an explicit bijection
    `Fix(step) ≃ Fix(costep)` given by `generate`, with inverse `modify`.
-/
def fixedEquiv (generate : R → E) (modify : E → R) :
    {r : R // step generate modify r = r} ≃ {e : E // costep generate modify e = e} where
  toFun r := ⟨generate r.1, generate_fixed_of_fixed generate modify r.2⟩
  invFun e := ⟨modify e.1, modify_fixed_of_fixed generate modify e.2⟩
  left_inv := fun r => Subtype.ext (by simpa [step] using r.2)
  right_inv := fun e => Subtype.ext (by simpa [costep] using e.2)

/-! ### 3. Recurrence duality: the fixed-period equivalence with explicit inverse -/

/--
Key computation: `generate (step^[m] (modify e)) = costep^[m+1] e`.
-/
theorem generate_step_modify (generate : R → E) (modify : E → R) (m : ℕ) (e : E) :
    generate ((step generate modify)^[m] (modify e)) =
      (costep generate modify)^[m + 1] e := by
  rw [generate_iterate generate modify m (modify e),
    show generate (modify e) = costep generate modify e from rfl,
    Function.iterate_succ_apply]

/--
The forward direction preserves `n`-periodicity.
-/
theorem perEquiv_toFun_spec (generate : R → E) (modify : E → R) (n : ℕ) {r : R}
    (h : (step generate modify)^[n] r = r) :
    (costep generate modify)^[n] (generate r) = generate r := by
  rw [ ← generate_iterate, h ]

/--
The backward direction lands on an `n`-periodic point.
-/
theorem perEquiv_invFun_spec (generate : R → E) (modify : E → R) (n : ℕ) (hn : 1 ≤ n)
    {e : E} (h : (costep generate modify)^[n] e = e) :
    (step generate modify)^[n] ((step generate modify)^[n - 1] (modify e)) =
      (step generate modify)^[n - 1] (modify e) := by
  rcases n with ( _ | n ) <;> simp_all +decide [ ← Function.iterate_add_apply, costep ];
  simp_all +decide [ step, Function.iterate_add_apply ];
  convert congr_arg _ ?_;
  convert congr_arg modify h using 1;
  exact congr_arg _ ( by exact Nat.recOn n rfl fun n ih => by simp +decide [ *, Function.iterate_succ_apply' ] )

/--
Left inverse identity for the period-`n` equivalence.
-/
theorem perEquiv_left (generate : R → E) (modify : E → R) (n : ℕ) (hn : 1 ≤ n) {r : R}
    (h : (step generate modify)^[n] r = r) :
    (step generate modify)^[n - 1] (modify (generate r)) = r := by
  cases n <;> aesop

/--
Right inverse identity for the period-`n` equivalence.
-/
theorem perEquiv_right (generate : R → E) (modify : E → R) (n : ℕ) (hn : 1 ≤ n) {e : E}
    (h : (costep generate modify)^[n] e = e) :
    generate ((step generate modify)^[n - 1] (modify e)) = e := by
  convert generate_step_modify generate modify ( n - 1 ) e using 1 ; rcases n with ( _ | _ | n ) <;> simp_all +decide [ Function.iterate_succ_apply' ]

/-- For period `n ≥ 1`, `n`-periodic points of the two layers biject; the forward
    map is `generate`, the explicit inverse is `e ↦ step^{n-1}(modify e)`. -/
def perEquiv (generate : R → E) (modify : E → R) (n : ℕ) (hn : 1 ≤ n) :
    {r : R // (step generate modify)^[n] r = r} ≃
    {e : E // (costep generate modify)^[n] e = e} where
  toFun r := ⟨generate r.1, perEquiv_toFun_spec generate modify n r.2⟩
  invFun e := ⟨(step generate modify)^[n - 1] (modify e.1),
    perEquiv_invFun_spec generate modify n hn e.2⟩
  left_inv := fun r => Subtype.ext (perEquiv_left generate modify n hn r.2)
  right_inv := fun e => Subtype.ext (perEquiv_right generate modify n hn e.2)

/-! ### 4. Recurrence rigidity (conjugacy of the full periodic-point sets) -/

/--
`generate` carries periodic points of `step` to periodic points of `costep`.
-/
theorem generate_mem_periodicPts (generate : R → E) (modify : E → R) {r : R}
    (h : r ∈ Function.periodicPts (step generate modify)) :
    generate r ∈ Function.periodicPts (costep generate modify) := by
  obtain ⟨ n, hn, hr ⟩ := h; use n; simp_all +decide [ Function.IsPeriodicPt, Function.IsFixedPt ] ;
  rw [ ← generate_iterate, hr ]

/-- The induced map on periodic points. -/
def genPeriodic (generate : R → E) (modify : E → R) :
    {r : R // r ∈ Function.periodicPts (step generate modify)} →
    {e : E // e ∈ Function.periodicPts (costep generate modify)} :=
  fun r => ⟨generate r.1, generate_mem_periodicPts generate modify r.2⟩

/--
The induced map on periodic points is bijective.
-/
theorem genPeriodic_bijective (generate : R → E) (modify : E → R) :
    Function.Bijective (genPeriodic generate modify) := by
  constructor;
  · intro x y hxy
    have h_eq : generate x.1 = generate y.1 := by
      injection hxy;
    obtain ⟨ m, hm ⟩ := x.2
    obtain ⟨ n, hn ⟩ := y.2
    have h_period : (step generate modify)^[m * n] x.1 = x.1 ∧ (step generate modify)^[m * n] y.1 = y.1 := by
      simp_all +decide [ Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_mul, Function.iterate_fixed ];
      rw [ ← Function.iterate_mul, mul_comm, Function.iterate_mul, Function.iterate_fixed hn.2 ];
    have h_step_eq : ∀ k : ℕ, k > 0 → (step generate modify)^[k] x.1 = (step generate modify)^[k] y.1 := by
      intro k hk; induction hk <;> simp_all +decide [ Function.iterate_succ_apply', step ] ;
    exact Subtype.ext ( h_period.1.symm.trans ( h_step_eq ( m * n ) ( Nat.mul_pos hm.1 hn.1 ) ▸ h_period.2 ) );
  · intro ⟨ e, he ⟩
    obtain ⟨ n, hn, he' ⟩ := he
    use ⟨ ( step generate modify ) ^[ n - 1] ( modify e ), by
      exact ⟨ n, hn, by simpa [ Function.iterate_succ_apply' ] using perEquiv_invFun_spec generate modify n hn he' ⟩ ⟩
    generalize_proofs at *;
    exact Subtype.ext ( perEquiv_right generate modify n hn he' )

/-- Recurrence rigidity: the full sets of periodic points biject. -/
noncomputable def periodicPtsEquiv (generate : R → E) (modify : E → R) :
    {r : R // r ∈ Function.periodicPts (step generate modify)} ≃
    {e : E // e ∈ Function.periodicPts (costep generate modify)} :=
  Equiv.ofBijective _ (genPeriodic_bijective generate modify)

/-- The cardinalities of the periodic-point sets agree. -/
theorem periodicPts_card_eq (generate : R → E) (modify : E → R) :
    Nonempty
      ({r : R // r ∈ Function.periodicPts (step generate modify)} ≃
       {e : E // e ∈ Function.periodicPts (costep generate modify)}) :=
  ⟨periodicPtsEquiv generate modify⟩

end RGF.Bilayer