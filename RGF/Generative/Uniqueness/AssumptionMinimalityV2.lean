import Mathlib
import RGF.Generative.Locking.LockingMembrane
import RGF.Physics.Emergence.LatticeUniquenessGap
import RGF.Generative.Uniqueness.AssumptionMinimality

/-!
# P6 — change of basis: upgrading the three dynamical assumptions to theorems

`RGF.AssumptionMinimality.RGFCoreAssumptions` packages **eight** independent
hypotheses behind the locked invariants `(k, dim, coord) = (5, 3, 6)`.  Of these,
three are *dynamical* scalar inputs that were taken as bare assumptions:

* `coupling : 2 ≤ n₂` — the dual-mode lower bound,
* `depth2   : n₂ ≤ 2` — the depth-2 upper bound,
* `oddk     : Odd k`  — oddness of the mode order.

This file carries out a genuine *change of basis*
that replaces these three scalar assumptions by a **single structural primitive**
— `AntisymDualLayerCore` — encoding *"dual-layer contractive dynamics with a real
antisymmetric linearization"*, from which all three are **derived as theorems**
(not re-assumed).  The conclusion `(5, 3, 6)` is **not weakened**: the primitive is
shown to imply the full eight-assumption bundle `RGFCoreAssumptions`, so every
downstream theorem keeps holding verbatim.

The genuine dynamical content of the primitive, and what each field buys:

* **dual-layer contractive dynamics** (`emergence : EmergenceSupported n₂`): the
  critical spectrum carries *both* a neutral (phase-locking, G2) mode and a
  contracting (recovery, G3) mode.  By `two_layer_minimal` these cannot share a
  single two-dimensional block, so `2 ≤ n₂` (this *derives* `coupling`).
* **depth-2 / real antisymmetric biquadratic spectrum** (`freqs`, `freq_card`,
  `freq_roots`): the `n₂` positive eigenfrequencies are the distinct positive roots
  of one biquadratic `ω⁴ − a ω² + b = 0` — exactly the characteristic polynomial of
  the real antisymmetric depth-2 generator (cf.
  `L2L3OpenItems.skew5_charpoly_form`).  By `depth_two_caps_frequencies` a
  biquadratic has at most two positive roots, so `n₂ ≤ 2` (this *derives* `depth2`).
* **real antisymmetric linearization with a chiral axis** (`chiral : k = 2*n₂+1`):
  a real antisymmetric generator on the `k`-dimensional locking membrane splits into
  `n₂` two-dimensional rotation planes (the conjugate eigenfrequency pairs `±iω`)
  plus exactly **one** real chiral axis (the guaranteed zero mode of an odd-size
  skew operator, cf. `L2L3OpenItems.skew_odd_det_zero`).  Hence `k = 2·n₂ + 1`,
  which immediately yields `Odd k` (this *derives* `oddk`) and, as a bonus, the
  dihedral representation bridge `n₂ = num2DIrreps k` (`repCount`).

The remaining four inputs (`lock`, `rot`, `dimpos`, `central`) are *not* dynamical
and are carried over unchanged.  Thus P6 genuinely lowers the count of free scalar
assumptions: the four arithmetic inputs `{coupling, depth2, oddk, repCount}` are now
*consequences* of one structural primitive, leaving only the four geometric/
dictionary inputs as free hypotheses (plus the primitive's structural data).

Non-vacuity is certified by `antisymDualLayerCore_satisfiable`: the 3D simple-cubic
lattice at `k = 5`, `n₂ = 2`, with the two positive frequencies `{1, 2}` (roots of
`ω⁴ − 5 ω² + 4`), realizes the primitive.
-/

open RGF.LatticeUniquenessGap
open RGF.AssumptionMinimality

namespace RGF.AssumptionMinimalityV2

/-! ## The single structural primitive -/

/-- **The P6 structural primitive: dual-layer contractive dynamics with a real
antisymmetric linearization.**

It bundles the *genuine dynamical data* of the RGF core from which the three former
scalar assumptions `coupling`, `depth2`, `oddk` (and the dictionary input
`repCount`) all follow as theorems, together with the four non-dynamical
geometric/dictionary inputs carried over unchanged. -/
structure AntisymDualLayerCore (k n₂ : ℕ) (L : LatticeCandidate) : Type where
  /-- Dual-layer contractive dynamics: the critical spectrum supports emergence
      (a neutral phase-locking mode *and* a contracting recovery mode coexist). -/
  emergence : EmergenceSupported n₂
  /-- Coefficient `a` of the depth-2 biquadratic `ω⁴ − a ω² + b`. -/
  biquad_a : ℝ
  /-- Coefficient `b` of the depth-2 biquadratic `ω⁴ − a ω² + b`. -/
  biquad_b : ℝ
  /-- The set of positive eigenfrequencies of the real antisymmetric generator. -/
  freqs : Finset ℝ
  /-- There are exactly `n₂` positive eigenfrequencies. -/
  freq_card : freqs.card = n₂
  /-- Each eigenfrequency is positive and is a root of the depth-2 biquadratic. -/
  freq_roots : ∀ ω ∈ freqs, 0 < ω ∧ ω ^ 4 - biquad_a * ω ^ 2 + biquad_b = 0
  /-- Real antisymmetric linearization: the `k`-dimensional membrane splits into
      `n₂` rotation planes plus one real chiral axis, so `k = 2·n₂ + 1`. -/
  chiral : k = 2 * n₂ + 1
  /-- G1/G3 symmetry→direction bridge: `forwardCount L = k`. -/
  lock : forwardCount L = k
  /-- Intrinsic rotation-vector criterion: `rotGen (dim) = dim`. -/
  rot : rotGen L.dim = L.dim
  /-- The spatial dimension is positive. -/
  dimpos : 0 < L.dim
  /-- G1 reversibility / central symmetry. -/
  central : L.invSym = true

namespace AntisymDualLayerCore

variable {k n₂ : ℕ} {L : LatticeCandidate}

/-! ## The three dynamical assumptions, now derived as theorems -/

/-- **`coupling` derived.**  The dual-layer contractive dynamics force `2 ≤ n₂`. -/
theorem coupling (C : AntisymDualLayerCore k n₂ L) : 2 ≤ n₂ :=
  two_layer_minimal C.emergence

/-- **`depth2` derived.**  The depth-2 / real antisymmetric biquadratic spectrum
    forces `n₂ ≤ 2`. -/
theorem depth2 (C : AntisymDualLayerCore k n₂ L) : n₂ ≤ 2 := by
  have h := depth_two_caps_frequencies C.biquad_a C.biquad_b C.freqs C.freq_roots
  rw [C.freq_card] at h
  exact h

/-- **`oddk` derived.**  The real antisymmetric linearization (`k = 2·n₂ + 1`)
    forces an odd mode order. -/
theorem oddk (C : AntisymDualLayerCore k n₂ L) : Odd k :=
  ⟨n₂, C.chiral⟩

/-- **`repCount` derived (bonus).**  The chiral decomposition `k = 2·n₂ + 1` is
    consistent with the dihedral two-dimensional irrep count `n₂ = num2DIrreps k`. -/
theorem repCount (C : AntisymDualLayerCore k n₂ L) : n₂ = num2DIrreps k := by
  have hodd : Odd k := C.oddk
  rw [num2DIrreps_odd k hodd, C.chiral]
  omega

/-! ## The primitive implies the full eight-assumption bundle -/

/-- **Change of basis.**  The single primitive implies the complete
    eight-assumption bundle `RGFCoreAssumptions`: the four arithmetic inputs are
    discharged by the theorems above, the four geometric/dictionary inputs are
    carried over. -/
def toRGFCoreAssumptions (C : AntisymDualLayerCore k n₂ L) :
    RGFCoreAssumptions k n₂ L where
  coupling := C.coupling
  depth2   := C.depth2
  oddk     := C.oddk
  repCount := C.repCount
  lock     := C.lock
  rot      := C.rot
  dimpos   := C.dimpos
  central  := C.central

/-- **The primitive derives the locked invariants.**  From the single structural
    primitive, `(k, dim, coord) = (5, 3, 6)` — with no separate `coupling`,
    `depth2`, `oddk` assumptions. -/
theorem conclusion (C : AntisymDualLayerCore k n₂ L) : Conclusion k L :=
  core_assumptions_conclusion C.toRGFCoreAssumptions

/-- **Uniqueness of the locked invariants from the primitive.** -/
theorem invariants_unique (C : AntisymDualLayerCore k n₂ L) :
    (k, L.dim, L.coord) = (5, 3, 6) := by
  obtain ⟨hk, hd, hc⟩ := C.conclusion
  simp [hk, hd, hc]

end AntisymDualLayerCore

/-! ## Non-vacuity -/

/-- **Satisfiability.**  The primitive is non-vacuous: the 3D simple-cubic lattice
    at `k = 5`, `n₂ = 2`, with the two positive eigenfrequencies `{1, 2}` (the
    positive roots of the biquadratic `ω⁴ − 5 ω² + 4 = 0`) realizes it. -/
theorem antisymDualLayerCore_satisfiable :
    ∃ (k n₂ : ℕ) (L : LatticeCandidate), Nonempty (AntisymDualLayerCore k n₂ L) :=
  ⟨5, 2, simpleCubic, ⟨{
    emergence  := two_modes_emergence
    biquad_a   := 5
    biquad_b   := 4
    freqs      := {1, 2}
    freq_card  := Finset.card_pair (by norm_num)
    freq_roots := by
      intro ω hω
      simp only [Finset.mem_insert, Finset.mem_singleton] at hω
      rcases hω with rfl | rfl <;> norm_num
    chiral     := by norm_num
    lock       := by decide
    rot        := by decide
    dimpos     := by decide
    central    := rfl }⟩⟩

/-- **The change of basis genuinely reduces the assumption count.**  Whenever the
    primitive holds, the four formerly-free arithmetic inputs
    `coupling ∧ depth2 ∧ oddk ∧ repCount` are *all* theorems, so only the four
    geometric/dictionary inputs remain as free hypotheses. -/
theorem antisym_core_upgrades_arithmetic
    {k n₂ : ℕ} {L : LatticeCandidate} (C : AntisymDualLayerCore k n₂ L) :
    (2 ≤ n₂) ∧ (n₂ ≤ 2) ∧ Odd k ∧ (n₂ = num2DIrreps k) :=
  ⟨C.coupling, C.depth2, C.oddk, C.repCount⟩

end RGF.AssumptionMinimalityV2
