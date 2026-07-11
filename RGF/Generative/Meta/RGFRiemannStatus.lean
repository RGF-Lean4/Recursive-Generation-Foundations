import Mathlib
import RGF.Generative.Locking.LockingNonDegeneracy

/-!
# The logical status of "locking non-degeneracy" relative to the Riemann Hypothesis

This module pins down, in fully machine-checked form, the *logical relationship*
between RGF's "locking non-degeneracy" (LND) statement and the Riemann Hypothesis
(RH).  The point is **not** to prove RH (we do not), but to clarify *what kind* of
statement the RGF↔RH link is:

* **§1 (definitional binding is trivial).**  In the original RGF text `LND s` was
  *defined* to be `Re s = 1/2`, and RH is the assertion that every nontrivial zero
  has `Re s = 1/2`.  So the original "LND ⇔ RH" is literally `Iff.rfl`: it carries
  no mathematical information (`definitional_binding_trivial`).

* **§2 (the one-sided ⇔ two-sided equivalence is not a logical tautology).**  For a
  *general* function the equivalence "all strip-zeros lie on the critical line" ⇔
  "there are no zeros in the right half of the strip" fails.  The explicit
  counterexample is `f(s) = s - 1/4` (`oneSided_iff_twoSided_not_universal`).  Hence
  any proof of the equivalence for `ζ` must use a genuine property of `ζ`.

* **§3 (for `ζ` the equivalence is a real theorem driven by the functional
  equation).**  Using only the functional equation (zero reflection `s ↦ 1 - s`)
  we obtain the substantive equivalences
  `riemannHypothesis_iff_oneSided` (`RH ↔ RH_≤`),
  the symmetric `riemannHypothesis_iff_oneSided_ge` (`RH ↔ RH_≥`),
  and `riemannHypothesis_tfae` bundling them with the strip form and with Mathlib's
  full `RiemannHypothesis`.  The bridge to Mathlib's `RiemannHypothesis`
  (`riemannHypothesis_iff_strip`) additionally uses the critical-strip embedding
  (no zeros for `Re s ≥ 1`, and zeros with `Re s ≤ 0` are trivial).

* **§4 (honest boundary).**  Every theorem here has the shape `RH ↔ Φ`.  None of
  them asserts the *truth* of RH or of any one-sided form; they are logical bridges
  only.

Here, in line with the project convention (`RGF.SpiralLocking.ZetaNontrivialZero`),
"nontrivial zero" means a zero of `ζ` in the open critical strip `0 < Re s < 1`,
and `RiemannHypothesis_strip` (from `LockingNonDegeneracy.lean`) is RH in that form.
The final bridge connects this to Mathlib's official `RiemannHypothesis`.
-/

namespace RGF.RiemannStatus

open Complex
open RGF.FORS (RiemannHypothesis_strip)

/-! ### §0  One-sided locking predicates (strip-localized) -/

/-- `RH_≤`: every zero of `ζ` in the open critical strip satisfies `Re s ≤ 1/2`. -/
def RHle : Prop := ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re ≤ 1 / 2

/-- `RH_≥`: every zero of `ζ` in the open critical strip satisfies `1/2 ≤ Re s`. -/
def RHge : Prop := ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → 1 / 2 ≤ s.re

/-! ### §1  Definitional binding is logically trivial -/

/-- The "locking non-degeneracy" predicate as originally *defined* in RGF:
    `LND s := Re s = 1/2`. -/
def LND (s : ℂ) : Prop := s.re = 1 / 2

/-- **Theorem 1 (definitional binding).**  Because `LND s` is *defined* to be
    `Re s = 1/2`, the statement "every nontrivial zero satisfies `LND`" is literally
    the same proposition as `RiemannHypothesis_strip`.  The proof is `Iff.rfl`: this
    equivalence carries no mathematical content. -/
theorem definitional_binding_trivial :
    RiemannHypothesis_strip ↔
      (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → LND s) :=
  Iff.rfl

/-! ### §2  The one-sided ⇔ two-sided equivalence is not a universal logical truth -/

/-- For an arbitrary function `f`, "all zeros in the strip lie on the line `Re = 1/2`". -/
def ZerosOnLine (f : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, f s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- For an arbitrary function `f`, "there are no zeros in the right half-strip
    `1/2 < Re s < 1`". -/
def NoRightZeros (f : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, f s = 0 → 1 / 2 < s.re → s.re < 1 → False

/-- **Theorem 2 (the equivalence is not a tautology).**  There is an (entire,
    indeed polynomial) function `f` for which `ZerosOnLine f` and `NoRightZeros f`
    are *not* equivalent.  Witness: `f(s) = s - 1/4`, whose unique zero `s = 1/4`
    sits in the left half-strip, so `NoRightZeros f` holds while `ZerosOnLine f`
    fails.  Consequently any proof of the equivalence for `ζ` must use a genuine
    property of `ζ` (its functional-equation symmetry about `Re s = 1/2`). -/
theorem oneSided_iff_twoSided_not_universal :
    ∃ f : ℂ → ℂ, ¬ (ZerosOnLine f ↔ NoRightZeros f) := by
  refine ⟨fun s => s - 1 / 4, ?_⟩
  intro h
  have hB : NoRightZeros (fun s => s - 1 / 4) := by
    intro s hs hlo _
    rw [sub_eq_zero] at hs
    rw [hs] at hlo
    norm_num at hlo
  have hA : ZerosOnLine (fun s => s - 1 / 4) := h.mpr hB
  have := hA (1 / 4) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

/-! ### §3  For `ζ` the equivalence is substantive (functional equation) -/

/-- **Lemma 1 (zero reflection `s ↦ 1 - s`).**  If `s` is a zero of `ζ` in the open
    critical strip, then so is `1 - s`.  This is the sole nontrivial input to the
    one-sided equivalences and comes directly from the functional equation
    `riemannZeta_one_sub`. -/
theorem zero_reflect (s : ℂ) (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (1 - s) = 0 ∧ 0 < (1 - s).re ∧ (1 - s).re < 1 := by
  rw [riemannZeta_one_sub]
  · aesop
  · intro n hn; norm_num [Complex.ext_iff] at hn; linarith
  · aesop

/-- **Theorem 3 (RH ↔ one-sided upper bound).**  Over the critical strip, RH is
    equivalent to the *single-sided* statement `RH_≤`.  The forward direction is
    immediate; the reverse direction uses `zero_reflect` (the functional equation):
    if `Re s ≤ 1/2` for all strip-zeros then applying this to `1 - s` gives
    `1 - Re s ≤ 1/2`, i.e. `Re s ≥ 1/2`, hence `Re s = 1/2`. -/
theorem riemannHypothesis_iff_oneSided : RiemannHypothesis_strip ↔ RHle := by
  constructor
  · intro h s hz h0 h1
    exact le_of_eq (h s hz h0 h1)
  · intro h s hz h0 h1
    refine le_antisymm (h s hz h0 h1) ?_
    have hr := zero_reflect s hz h0 h1
    have := h (1 - s) hr.1 (by simpa using hr.2.1) (by simpa using hr.2.2)
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith

/-- **Theorem 3′ (RH ↔ one-sided lower bound).**  The symmetric statement: RH is
    equivalent to `RH_≥`. -/
theorem riemannHypothesis_iff_oneSided_ge : RiemannHypothesis_strip ↔ RHge := by
  constructor
  · intro h s hz h0 h1
    exact ge_of_eq (h s hz h0 h1)
  · intro h s hz h0 h1
    refine le_antisymm ?_ (h s hz h0 h1)
    have hr := zero_reflect s hz h0 h1
    have := h (1 - s) hr.1 (by simpa using hr.2.1) (by simpa using hr.2.2)
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith

/-! #### Bridge to Mathlib's official `RiemannHypothesis` -/

/-- **Lemma 3 (critical-strip embedding).**  Every nontrivial zero of `ζ`
    (a zero that is neither a trivial zero `-2(n+1)` nor `s = 1`) lies in the open
    critical strip `0 < Re s < 1`.  Upper bound: `riemannZeta_ne_zero_of_one_le_re`.
    Lower bound: if `Re s ≤ 0`, the functional equation forces `cos (π (1-s) / 2) = 0`
    (since `ζ(1-s) ≠ 0` for `Re(1-s) ≥ 1` and `Γ` never vanishes), whence `1 - s` is
    an odd integer `≥ 3` and `s = -2(n+1)` is a trivial zero — a contradiction.

    (The hypothesis `s ≠ 1` turns out to be unnecessary: it is already implied by
    `riemannZeta s = 0`, since `ζ` does not vanish at its pole.) -/
theorem nontrivial_zero_in_strip (s : ℂ) (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · contrapose! htriv
    -- Let `w := 1 - s`, so `w.re = 1 - s.re ≥ 1`.
    set w : ℂ := 1 - s
    have hw_re : w.re ≥ 1 := by aesop
    have hw_ne_neg_n : ∀ n : ℕ, w ≠ -n := by
      intro n hn; norm_num [Complex.ext_iff] at hn; linarith
    have hw_ne_one : w ≠ 1 := by grind +suggestions
    have hw_eq : riemannZeta (1 - w) =
        2 * (2 * Real.pi) ^ (-w) * Gamma w * Complex.cos (Real.pi * w / 2) * riemannZeta w := by
      convert riemannZeta_one_sub hw_ne_neg_n hw_ne_one using 1
    -- The only factor that can vanish is `cos (π * w / 2)`.
    have h_cos_zero : Complex.cos (Real.pi * w / 2) = 0 := by
      have h_zeta_ne : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw_re
      simp +zetaDelta at *
      simp_all +decide [Complex.Gamma_ne_zero, Complex.cpow_def]
    -- `cos (π w / 2) = 0` gives `w = 2k+1` for some integer `k`.
    obtain ⟨k, hk⟩ : ∃ k : ℤ, w = 2 * k + 1 := by
      refine Complex.cos_eq_zero_iff.mp h_cos_zero |> fun ⟨k, hk⟩ => ⟨k, ?_⟩
      norm_num [Complex.ext_iff] at *
      constructor <;> nlinarith [Real.pi_pos]
    rcases k with ⟨_ | k⟩ <;> norm_num at *
    · contradiction
    · grind +splitIndPred
    · norm_num [Complex.ext_iff] at *; linarith
  · exact lt_of_not_ge fun h => absurd hz (riemannZeta_ne_zero_of_one_le_re h)

/-- **Theorem 4 (RH ↔ strip form).**  Mathlib's official `RiemannHypothesis` is
    equivalent to `RiemannHypothesis_strip`.  Forward: a strip zero is nontrivial and
    `≠ 1`.  Reverse: by `nontrivial_zero_in_strip` every nontrivial zero lies in the
    strip, where `RiemannHypothesis_strip` applies. -/
theorem riemannHypothesis_iff_strip : RiemannHypothesis ↔ RiemannHypothesis_strip := by
  constructor
  · intro h s hz h0 h1
    refine h s hz ?_ ?_
    · rintro ⟨n, rfl⟩; norm_num at h0 h1; linarith
    · rintro rfl; norm_num at h1
  · intro h s hz htriv hne1
    obtain ⟨h0, h1⟩ := nontrivial_zero_in_strip s hz htriv
    exact h s hz h0 h1

/-- **Theorem 5 (unified equivalences).**  The full Riemann Hypothesis, its
    strip form, and the two single-sided forms are all equivalent. -/
theorem riemannHypothesis_tfae :
    List.TFAE [RiemannHypothesis, RiemannHypothesis_strip, RHle, RHge] := by
  tfae_have 1 ↔ 2 := riemannHypothesis_iff_strip
  tfae_have 2 ↔ 3 := riemannHypothesis_iff_oneSided
  tfae_have 2 ↔ 4 := riemannHypothesis_iff_oneSided_ge
  tfae_finish

/-! ### §4  Honest boundary

All statements above are of the form `RH ↔ Φ`.  None of them asserts that RH (or any
one-sided reformulation) is *true*.  They establish logical bridges only: the RGF
"locking non-degeneracy ⇔ RH" link is upgraded from a trivial definitional alignment
(§1) to a substantive equivalence genuinely driven by the functional equation (§3),
while leaving the truth of RH itself entirely open. -/

end RGF.RiemannStatus
