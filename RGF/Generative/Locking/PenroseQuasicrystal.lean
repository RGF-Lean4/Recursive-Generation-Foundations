/-
  RGF/PenroseQuasicrystal.lean

  Direction III — Quasicrystal dynamic growth and local/global consistency, plus
  the cellular-automaton (Wolfram-model) interface.

  `CrystallographicRestriction.lean` proves that five-fold symmetry is *forbidden*
  in a two-dimensional periodic lattice.  The complementary positive statement is
  that a purely *local* generation rule with an irrational (golden-ratio) slope
  produces a **globally aperiodic** order — the one-dimensional cut-and-project /
  Sturmian model underlying Penrose tilings (via de Bruijn's projection method).

  Contents (namespace `RGF.Penrose`):

  1. **Cut-and-project / Sturmian word.**  `stur α n = ⌊(n+1)α⌋ − ⌊nα⌋` is the
     canonical mechanical word obtained by projecting the integer lattice through
     a line of slope `α` (the 1-D de Bruijn scheme).  We prove the telescoping
     density law `∑_{n<N} stur α n = ⌊Nα⌋` (`stur_sum`) and the key
     **aperiodicity theorem** `stur_aperiodic`: for irrational `α` the generated
     word has *no* period — a globally non-periodic structure produced by a purely
     local rule.

  2. **Golden-ratio (five-fold) instance.**  The golden slope
     `γ = (√5 − 1)/2 = 1/φ` is irrational (`irrational_fibSlope`), so the induced
     "Fibonacci quasicrystal" is aperiodic (`fibonacci_word_aperiodic`).  This is
     the five-fold-symmetric aperiodic order excluded from periodic lattices.

  3. **Cellular-automaton / Wolfram-model interface.**  Elementary cellular
     automata are formalised as local update rules on bi-infinite binary
     configurations; we prove shift-equivariance (`ca_shift_equivariant`, the
     Curtis–Hedlund locality property) and determinism of the evolution, and give
     "Rule 110" — the canonical Turing-complete elementary CA — as a concrete
     instance.

  Everything is `sorry`-free once discharged.
-/
import Mathlib

open Finset BigOperators

namespace RGF.Penrose

/-! ## 1. Cut-and-project (Sturmian) word -/

/-- The mechanical / Sturmian word of slope `α`: the projected-lattice increment
    `stur α n = ⌊(n+1)α⌋ − ⌊nα⌋`. -/
noncomputable def stur (α : ℝ) (n : ℕ) : ℤ :=
  ⌊((n : ℝ) + 1) * α⌋ - ⌊(n : ℝ) * α⌋

/-
**Telescoping density law.** The partial sums of the Sturmian word recover the
    Beatty counting function: `∑_{n<N} stur α n = ⌊Nα⌋`.
-/
theorem stur_sum (α : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, stur α n = ⌊(N : ℝ) * α⌋ := by
  convert Finset.sum_range_sub ( fun n => ⌊ ( n : ℝ ) * α⌋ ) N using 1 ; norm_num [ stur ];
  norm_num

/-
Sum of a `p`-periodic Sturmian word over `k` full periods is `k` times the
    sum over one period.
-/
theorem stur_sum_periods (α : ℝ) {p : ℕ}
    (hper : ∀ n, stur α (n + p) = stur α n) (k : ℕ) :
    ∑ n ∈ Finset.range (k * p), stur α n
      = k * ∑ n ∈ Finset.range p, stur α n := by
  induction' k with k ih;
  · norm_num;
  · rw [ Nat.succ_mul, Finset.sum_range_add, ih ];
    simp +decide [ add_mul ];
    exact Finset.sum_congr rfl fun x hx => Nat.recOn k ( by norm_num ) fun n ihn => by rw [ Nat.succ_mul, ← add_right_comm, hper, ihn ] ;

/-
**Aperiodicity of the cut-and-project word.** For irrational slope `α`, the
    Sturmian word has no period: a purely local generation rule yields a globally
    non-periodic (quasicrystalline) structure.
-/
theorem stur_aperiodic (α : ℝ) (hα : Irrational α) :
    ¬ ∃ p : ℕ, 0 < p ∧ ∀ n, stur α (n + p) = stur α n := by
  -- Assume ⟨p, hp, hper⟩ with hp : 0 < p and hper : ∀ n, stur α (n+p) = stur α n.
  by_contra h
  obtain ⟨p, hp_pos, hp_period⟩ := h
  set c := ∑ n ∈ Finset.range p, stur α n
  have hc : c = ⌊(p : ℝ) * α⌋ := by
    convert stur_sum α p using 1
  have h_floor_key : ∀ k : ℕ, ⌊((k * p : ℕ) : ℝ) * α⌋ = k * c := by
    intros k
    have := stur_sum α (k * p)
    have := stur_sum_periods α hp_period k
    aesop;
  -- Show δ = 0: if δ > 0, by the archimedean property (`exists_nat_gt`) pick k with (k:ℝ) > 1/δ; then (k:ℝ)*δ > 1, contradicting (k:ℝ)*δ < 1. Hence δ = 0, i.e. (p:ℝ)*α = (c:ℝ), so α = (c:ℝ)/(p:ℝ).
  have h_delta_zero : (p : ℝ) * α = c := by
    -- By contradiction, assume δ > 0.
    by_contra h_delta_pos
    have h_delta_pos' : 0 < (p : ℝ) * α - c := by
      exact sub_pos_of_lt ( lt_of_le_of_ne ( by exact_mod_cast hc ▸ Int.floor_le _ ) ( Ne.symm h_delta_pos ) );
    -- Choose k such that k * δ > 1.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℝ) * ((p : ℝ) * α - c) > 1 := by
      exact ⟨ ⌊1 / ( p * α - c ) ⌋₊ + 1, by push_cast; nlinarith [ Nat.lt_floor_add_one ( 1 / ( p * α - c ) ), mul_div_cancel₀ 1 h_delta_pos'.ne' ] ⟩;
    have := h_floor_key k; rw [ Int.floor_eq_iff ] at this; push_cast at *; nlinarith;
  exact hα ⟨ c / p, by push_cast; rw [ ← h_delta_zero, mul_div_cancel_left₀ _ ( by positivity ) ] ⟩

/-! ## 2. Golden-ratio (five-fold) quasicrystal -/

/-- The golden slope `γ = (√5 − 1)/2 = 1/φ`. -/
noncomputable def fibSlope : ℝ := (Real.sqrt 5 - 1) / 2

/-
The golden slope is irrational.
-/
theorem irrational_fibSlope : Irrational fibSlope := by
  exact_mod_cast Nat.Prime.irrational_sqrt ( by norm_num ) |> Irrational.sub_ratCast 1 |> Irrational.div_ratCast <| by norm_num;

/-- **Five-fold aperiodic order.** The golden-ratio ("Fibonacci") quasicrystal
    generated by the local cut-and-project rule is globally aperiodic — the
    positive counterpart of the crystallographic exclusion of five-fold symmetry
    from periodic lattices. -/
theorem fibonacci_word_aperiodic :
    ¬ ∃ p : ℕ, 0 < p ∧ ∀ n, stur fibSlope (n + p) = stur fibSlope n :=
  stur_aperiodic fibSlope irrational_fibSlope

/-! ## 3. Cellular-automaton / Wolfram-model interface -/

/-- A bi-infinite binary configuration. -/
abbrev Config := ℤ → Bool

/-- The left shift on configurations. -/
def shift (c : Config) : Config := fun i => c (i + 1)

/-- The one-step update of an elementary cellular automaton with local rule
    `rule : Bool → Bool → Bool → Bool` (depending on the left neighbour, the
    cell, and the right neighbour). -/
def caStep (rule : Bool → Bool → Bool → Bool) (c : Config) : Config :=
  fun i => rule (c (i - 1)) (c i) (c (i + 1))

/-- **Curtis–Hedlund locality / shift-equivariance.** The CA update commutes with
    the shift: local rules generate translation-invariant global dynamics. -/
theorem ca_shift_equivariant (rule : Bool → Bool → Bool → Bool) (c : Config) :
    caStep rule (shift c) = shift (caStep rule c) := by
  funext i
  have h1 : i - 1 + 1 = i + 1 - 1 := by ring
  simp only [caStep, shift, h1]

/-- **Determinism.** The CA evolution is a genuine function of the initial
    configuration: equal initial data give equal trajectories. -/
theorem ca_deterministic (rule : Bool → Bool → Bool → Bool) (c d : Config)
    (h : c = d) (t : ℕ) : (caStep rule)^[t] c = (caStep rule)^[t] d := by
  rw [h]

/-- The local rule of the (Turing-complete) elementary cellular automaton
    **Rule 110**: `new = (l ∧ ¬c ∧ ¬r) ∨ (¬(l ∧ c ∧ r) ∧ (c ∨ r))` — equivalently,
    the truth table `01101110₂ = 110`. -/
def rule110 (l c r : Bool) : Bool :=
  match l, c, r with
  | true,  true,  true  => false
  | true,  true,  false => true
  | true,  false, true  => true
  | true,  false, false => false
  | false, true,  true  => true
  | false, true,  false => true
  | false, false, true  => true
  | false, false, false => false

/-- Rule 110 has the expected truth-table value on a representative input. -/
theorem rule110_example : rule110 true false true = true := rfl

end RGF.Penrose