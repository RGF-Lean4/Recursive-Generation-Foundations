/-
  RequestProject/OriginalMathematics.lean

  Original Mathematics IV — the recursive constitutive evolution semigroup,
  the mathematical flesh of "generation is irreversible".

  New structure:
      ConstitutiveEvolution := { λ ∈ ℂ : 0 < |λ| < 1 }
    * modulus `< 1` encodes the locking membrane (strict contraction);
    * argument encodes mode-locking (discrete symmetry);
    * closed under multiplication but *without an identity* (`1 ∉ CE`);
    * the precise mathematical incarnation of irreversible generation.

  Core theorems:
    1. Recurrence obstruction: the orbit `n ↦ λⁿ` is injective — the system
       never returns to a previous state.
    2. No trivial evolution: there is no multiplicative identity.
    3. Quasi-periodicity inside the membrane: if the argument is a primitive
       root of unity, the orbit's phase is periodic but the amplitude strictly
       decays — phase ordered, amplitude vanishing, the whole never repeats.
    4. Realizability: for any action `a > 0` and any lock order `p ≥ 1`, there is
       a `λ` with exactly that action and a primitive `p`-th-root argument — the
       parameter space is completely filled.
-/
import Mathlib

namespace RGF.ConstitutiveEvolution

open Complex

/-- The constitutive-evolution set: complex numbers strictly inside the punctured
    unit disk. -/
def CE : Set ℂ := {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1}

theorem mem_CE {z : ℂ} : z ∈ CE ↔ 0 < ‖z‖ ∧ ‖z‖ < 1 := Iff.rfl

theorem ne_zero_of_mem {z : ℂ} (hz : z ∈ CE) : z ≠ 0 := by
  rw [mem_CE] at hz
  intro h; rw [h] at hz; simp at hz

/-- The set is closed under multiplication. -/
theorem mul_mem {a b : ℂ} (ha : a ∈ CE) (hb : b ∈ CE) : a * b ∈ CE := by
  rw [mem_CE] at ha hb ⊢
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  rw [norm_mul]
  constructor
  · positivity
  · nlinarith [ha0, ha1, hb0, hb1]

/-! ### 1. Recurrence obstruction: the orbit is injective. -/

/--
The orbit `n ↦ λⁿ` is injective: the system never returns to a previous
    state.
-/
theorem orbit_injective {z : ℂ} (hz : z ∈ CE) :
    Function.Injective (fun n : ℕ => z ^ n) := by
  intro m n hmn;
  apply_fun Complex.normSq at hmn ; simp_all +decide [ Complex.normSq_eq_norm_sq ];
  rw [ pow_right_inj₀ ] at hmn <;> nlinarith [ hz.1, hz.2, norm_nonneg z ]

/-! ### 2. No trivial evolution: no multiplicative identity. -/

/--
There is no element of `CE` acting as a multiplicative identity on `CE`.
-/
theorem no_identity : ¬ ∃ e ∈ CE, ∀ z ∈ CE, e * z = z := by
  simp +zetaDelta at *;
  intro x hx;
  refine' ⟨ 1 / 2, _, _ ⟩ <;> norm_num [ hx ];
  · exact ⟨ by norm_num, by norm_num ⟩;
  · exact fun h => by rw [ h ] at hx; exact absurd hx ( by norm_num [ CE ] ) ;

/-! ### 3. Quasi-periodicity inside the locking membrane. -/

/--
Amplitude strictly decays along the orbit.
-/
theorem amplitude_strict_decay {z : ℂ} (hz : z ∈ CE) (n : ℕ) :
    ‖z ^ (n + 1)‖ < ‖z ^ n‖ := by
  norm_num [ pow_succ ];
  exact mul_lt_of_lt_one_right ( pow_pos ( norm_pos_iff.mpr ( ne_zero_of_mem hz ) ) _ ) hz.2

/--
If the normalized phase is a `p`-th root of unity, the orbit's direction is
    `p`-periodic: `z^(n+p)` points the same way as `z^n`.
-/
theorem phase_periodic {z : ℂ} (_hz : z ∈ CE) (p : ℕ)
    (hphase : ((z / (‖z‖ : ℂ)) ^ p = 1)) (n : ℕ) :
    z ^ (n + p) / (‖z ^ (n + p)‖ : ℂ) = z ^ n / (‖z ^ n‖ : ℂ) := by
  convert congr_arg ( fun x : ℂ => z ^ n / ‖z ^ n‖ * x ) hphase using 1 <;> ring_nf ; norm_cast ; norm_num [ pow_add, pow_mul ] ; ring_nf;

/-! ### 4. Realizability: the parameter space is completely filled. -/

/--
For any action `a > 0` and lock order `p ≥ 1` there is a `λ ∈ CE` with
    modulus `e^{-a}` and a primitive `p`-th-root-of-unity argument.
-/
theorem realizability (a : ℝ) (ha : 0 < a) (p : ℕ) (hp : 1 ≤ p) :
    ∃ z ∈ CE, ‖z‖ = Real.exp (-a) ∧
      IsPrimitiveRoot (z / (‖z‖ : ℂ)) p := by
  refine' ⟨ Real.exp ( -a ) * Complex.exp ( 2 * Real.pi * Complex.I / p ), _, _, _ ⟩ <;> norm_num [ Complex.norm_exp ];
  · refine' ⟨ _, _ ⟩ <;> norm_num [ Complex.norm_exp ];
    · positivity;
    · grind;
  · exact Complex.isPrimitiveRoot_exp _ ( by positivity )

end RGF.ConstitutiveEvolution