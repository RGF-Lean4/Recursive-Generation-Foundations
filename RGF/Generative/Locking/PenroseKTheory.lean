/-
  RGF/PenroseKTheory.lean

  Direction IV — Topological invariants of quasicrystals (K-theory) and cellular
  automata.

  This module records two structural pillars of the aperiodic-order programme
  inside RGF:

  1.  **K-theory of the Penrose C*-algebra (the golden dimension group).**
      Modelling the Penrose tiling algebra as the AF-algebra with Fibonacci
      connecting matrix `M = !![1,1;1,0]`, the ordered `K₀`-group is the golden
      dimension group `ℤ[φ]`.  We realise it via the trace embedding
      `emb : ℤ² → ℝ, (a,b) ↦ a + bφ`.  We prove the golden relation `φ² = φ+1`,
      that `(φ,1)` is the Perron eigenvector of `M` (`fib_eigenvector`), that
      `emb` is an injective additive homomorphism (so `K₀ ≅ ℤ²` has rank 2,
      `emb_injective`/`emb_add`), that the image `ℤ[φ]` is closed under
      multiplication (`emb_mul`, the golden-ring structure), and the tile-frequency
      / gap-labelling identities `1/φ + 1/φ² = 1` and `1/φ = φ-1`
      (`freq_sum`/`inv_phi`).

  2.  **Rule 110 gliders and the static ether.**  Elementary cellular automata
      are formalised as local update rules on bi-infinite binary configurations.
      We prove that the all-`false` background is a static solution
      (`static_ether`), that the evolution commutes with spatial translation
      (`caStep_shift`, `caStep_iterate_shift`, the Curtis–Hedlund locality), and
      that the spatial translate of a glider is again a glider (`glider_shift`).
      (A full Turing-completeness proof of Rule 110 in the Cook–Wolfram sense is
      beyond the present scope, as noted here.)

  Everything is `sorry`-free.
-/
import Mathlib

open Real
open Matrix

namespace RGF.PenroseK

/-! ## 1. The golden dimension group `ℤ[φ]` (K-theory of the Penrose algebra) -/

/-- The golden relation `φ² = φ + 1`. -/
theorem golden_relation : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq

/-- The Fibonacci connecting matrix `M = !![1,1;1,0]` of the AF-algebra whose
    `K₀`-group is the Penrose dimension group. -/
def fibMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]

/-- The Perron eigenvector `(φ, 1)` of the Fibonacci connecting matrix, with
    eigenvalue the golden ratio `φ`. -/
theorem fib_eigenvector :
    fibMatrix.mulVec ![goldenRatio, 1] = goldenRatio • ![goldenRatio, 1] := by
  funext i
  fin_cases i
  all_goals simp [fibMatrix, Matrix.mulVec, Fin.sum_univ_two, dotProduct]
  all_goals nlinarith [goldenRatio_sq]

/-- The trace embedding realising the ordered `K₀`-group of the Penrose algebra:
    `emb (a,b) = a + bφ`. -/
noncomputable def emb (p : ℤ × ℤ) : ℝ := (p.1 : ℝ) + (p.2 : ℝ) * goldenRatio

/-- `emb` is an additive homomorphism (the `K₀`-group is `(ℤ², +)`). -/
theorem emb_add (p q : ℤ × ℤ) : emb (p + q) = emb p + emb q := by
  simp only [emb, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

/-- `emb` is injective, so the dimension group `K₀ ≅ ℤ²` has rank `2`. -/
theorem emb_injective : Function.Injective emb := by
  intro p q h
  by_cases h_cases : p.2 = q.2
  · unfold emb at h; aesop
  · contrapose! h_cases
    unfold emb at *
    simp_all +decide
    by_contra h_neq
    have h_irr : Irrational goldenRatio := Real.goldenRatio_irrational
    exact h_irr ⟨(q.1 - p.1) / (p.2 - q.2), by
      push_cast
      rw [div_eq_iff (sub_ne_zero_of_ne <| by aesop)]
      linarith⟩

/-- The golden-ring multiplication law: the image `ℤ[φ]` is closed under
    multiplication, `(a+bφ)(c+dφ) = (ac+bd) + (ad+bc+bd)φ`. -/
theorem emb_mul (a b c d : ℤ) :
    emb (a, b) * emb (c, d) = emb (a * c + b * d, a * d + b * c + b * d) := by
  simp only [emb]
  push_cast
  linear_combination ((b : ℝ) * d) * goldenRatio_sq

/-- Gap-labelling / frequency identity: `1/φ = φ - 1`. -/
theorem inv_phi : 1 / goldenRatio = goldenRatio - 1 := by
  have h0 : goldenRatio ≠ 0 := goldenRatio_ne_zero
  rw [div_eq_iff h0]; nlinarith [goldenRatio_sq]

/-- Tile-frequency identity: `1/φ + 1/φ² = 1`. -/
theorem freq_sum : 1 / goldenRatio + 1 / goldenRatio ^ 2 = 1 := by
  have h0 : goldenRatio ≠ 0 := goldenRatio_ne_zero
  have e1 : 1 / goldenRatio = goldenRatio - 1 := inv_phi
  have e2 : 1 / goldenRatio ^ 2 = 2 - goldenRatio := by
    rw [div_eq_iff (pow_ne_zero 2 h0)]; nlinarith [goldenRatio_sq]
  rw [e1, e2]; ring

/-! ## 2. Rule 110 gliders and the static ether -/

/-- A bi-infinite binary configuration of an elementary cellular automaton. -/
def Config : Type := ℤ → Bool

/-- Spatial translation of a configuration by `k`. -/
def shiftBy (k : ℤ) (c : Config) : Config := fun x => c (x + k)

/-- One step of an elementary cellular automaton with local rule `rule`. -/
def caStep (rule : Bool → Bool → Bool → Bool) (c : Config) : Config :=
  fun x => rule (c (x - 1)) (c x) (c (x + 1))

/-- The evolution commutes with spatial translation (Curtis–Hedlund locality). -/
theorem caStep_shift (rule : Bool → Bool → Bool → Bool) (k : ℤ) (c : Config) :
    caStep rule (shiftBy k c) = shiftBy k (caStep rule c) := by
  funext x
  simp only [caStep, shiftBy]
  congr 1 <;> ring_nf

/-- Two spatial translations compose additively. -/
theorem shiftBy_shiftBy (j k : ℤ) (c : Config) :
    shiftBy j (shiftBy k c) = shiftBy (j + k) c := by
  funext x; simp only [shiftBy]; ring_nf

/-- Iterated evolution commutes with spatial translation. -/
theorem caStep_iterate_shift (rule : Bool → Bool → Bool → Bool) (n : ℕ) (k : ℤ)
    (c : Config) :
    (caStep rule)^[n] (shiftBy k c) = shiftBy k ((caStep rule)^[n] c) := by
  induction n generalizing c with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, caStep_shift, ih]

/-- A glider: a configuration that after `n > 0` steps returns to itself up to a
    spatial translation (a spacetime-translation-periodic configuration). -/
def IsGlider (rule : Bool → Bool → Bool → Bool) (g : Config) : Prop :=
  ∃ (n : ℕ) (k : ℤ), 0 < n ∧ (caStep rule)^[n] g = shiftBy k g

/-- The spatial translate of a glider is again a glider. -/
theorem glider_shift (rule : Bool → Bool → Bool → Bool) (g : Config) (j : ℤ)
    (h : IsGlider rule g) : IsGlider rule (shiftBy j g) := by
  obtain ⟨n, k, hn, hg⟩ := h
  refine ⟨n, k, hn, ?_⟩
  rw [caStep_iterate_shift, hg, shiftBy_shiftBy, shiftBy_shiftBy, Int.add_comm]

/-- The Rule 110 local update function. -/
def rule110 : Bool → Bool → Bool → Bool
  | true,  true,  true  => false
  | true,  true,  false => true
  | true,  false, true  => true
  | true,  false, false => false
  | false, true,  true  => true
  | false, true,  false => true
  | false, false, true  => true
  | false, false, false => false

/-- The all-`false` background (the static "ether"). -/
def ether : Config := fun _ => false

/-- The all-`false` background is a static solution of Rule 110. -/
theorem static_ether : caStep rule110 ether = ether := by
  funext x
  simp [caStep, ether, rule110]

end RGF.PenroseK