/-
  RGF/Generative/Meta/GenerativeFalsifiability.lean
    (module `RGF.Generative.Meta.GenerativeFalsifiability`)

  **§1 — Making the "generative step" predicate falsifiable.**

  The universality theorem `dual_layer_universality`
  (`RGF/Generative/Meta/RGFUniversality.lean`) shows that *every* self-map
  `f : X → X` is the `step` of some `RGFDualLayer` (take `modify = id`).  As a
  consequence the property "is an RGF generation step" is satisfied by *every*
  discrete system and therefore carries **zero discriminating information**: it can
  never be violated, so a proof that "the set-theoretic successor is such a step"
  is a tautology, not evidence.

  This file replaces that vacuous predicate by an honest, *constrained* one and
  proves that it is **falsifiable**: there is an explicit map that is provably
  **not** a generation step.  Only once the predicate can be violated does
  "operator `X` is a generation step" become genuine evidence rather than a
  synonym.

  The constrained generation predicate `IsGenerativeStep` bundles the three
  independent requirements demanded by the plan:

    * **finite alphabet** — states range over a fixed finite primitive set
      (`Alph = Fin 2`);
    * **locality** — one step reads only a *bounded* window of the state
      (radius `r`);
    * **determinism** — a single fixed rule `g` with no free parameters.

  Results:

    * `id_isGenerativeStep`, `shift_isGenerativeStep` — positive witnesses
      (the identity and the shift *are* generation steps);
    * `stepOf_local` — the defining locality property (a step at cell `n` depends
      only on cells `n … n+r`);
    * `lookahead_not_generativeStep` — the **non-triviality / falsifiability
      theorem**: the unbounded–look-ahead map `c ↦ (n ↦ c (2n))` is *not* a
      generation step for any radius or rule;
    * `generativeStep_not_universal` — hence, unlike `dual_layer_universality`,
      **not every** map is a generation step: the predicate genuinely splits the
      world in two.
-/
import Mathlib

namespace RGF
namespace Generative
namespace Falsifiability

/-- The fixed **finite primitive set** over which generation happens.  Any fixed
finite type would do; `Fin 2` is the minimal non-degenerate choice. -/
abbrev Alph : Type := Fin 2

/-- A one-dimensional **configuration**: a state assigning a primitive to every
cell of the discrete line `ℕ`. -/
abbrev Config : Type := ℕ → Alph

/-- The self-map induced by a **local rule** of radius `r`: the new value at cell
`n` is computed by the fixed rule `g` from the window `c n, c (n+1), …, c (n+r)`.
This is deterministic (a single `g`), local (window of width `r+1`) and ranges over
the finite alphabet `Alph`. -/
def stepOf (r : ℕ) (g : (Fin (r + 1) → Alph) → Alph) : Config → Config :=
  fun c n => g (fun j => c (n + j))

/-- **The honest, constrained generation predicate.**  A map `F : Config → Config`
counts as an RGF generation step iff it is induced by *some* finite-radius local
rule over the fixed finite alphabet.  Contrast with `RGFDualLayer.step`, which by
`dual_layer_universality` every map satisfies: this predicate is designed to be
*violable*. -/
def IsGenerativeStep (F : Config → Config) : Prop :=
  ∃ (r : ℕ) (g : (Fin (r + 1) → Alph) → Alph), F = stepOf r g

/-! ## Positive witnesses -/

/-- The identity map is a generation step (radius `0`, rule = read the single
window cell). -/
theorem id_isGenerativeStep : IsGenerativeStep (id : Config → Config) := by
  refine ⟨0, fun w => w 0, ?_⟩
  funext c n
  simp [stepOf]

/-- The left shift `c ↦ (n ↦ c (n+1))` is a generation step (radius `1`, rule =
read the second window cell). -/
theorem shift_isGenerativeStep :
    IsGenerativeStep (fun c => (fun n => c (n + 1))) := by
  refine ⟨1, fun w => w 1, ?_⟩
  funext c n
  simp [stepOf]

/-! ## Locality — the defining structural property -/

/-- **Locality of a generation step.**  The value of `stepOf r g c` at cell `n`
depends only on the window `c n, …, c (n+r)`: if two configurations agree on that
window they produce the same output at `n`. -/
theorem stepOf_local (r : ℕ) (g : (Fin (r + 1) → Alph) → Alph)
    (c d : Config) (n : ℕ) (h : ∀ j : Fin (r + 1), c (n + j) = d (n + j)) :
    stepOf r g c n = stepOf r g d n := by
  unfold stepOf
  congr 1
  funext j
  exact h j

/-! ## The falsifiability theorem -/

/-- The **unbounded–look-ahead map** `c ↦ (n ↦ c (2n))`.  Its output at cell `n`
reads cell `2n`, which for large `n` lies arbitrarily far outside any fixed window
`n … n+r`; hence it cannot be local. -/
def lookahead : Config → Config := fun c n => c (2 * n)

/-- **Non-triviality / falsifiability.**  The look-ahead map is *not* a generation
step for any radius or rule.  This is the theorem that gives the predicate content:
`IsGenerativeStep` is a property some maps *fail*, so establishing it for a genuine
operator is evidence rather than a tautology. -/
theorem lookahead_not_generativeStep : ¬ IsGenerativeStep lookahead := by
  rintro ⟨r, g, hF⟩
  -- Evaluate at cell `n = r + 1`, whose look-ahead target `2n = 2r+2` is beyond
  -- the window `n … n+r = (r+1) … (2r+1)`.
  -- Two configurations agreeing everywhere except at cell `2*(r+1)`.
  let c : Config := fun _ => (0 : Alph)
  let d : Config := fun k => if k = 2 * (r + 1) then (1 : Alph) else 0
  -- They agree on the whole window `(r+1) … (2r+1)`.
  have hwin : ∀ j : Fin (r + 1), c ((r + 1) + j) = d ((r + 1) + j) := by
    intro j
    have hj : (r + 1) + (j : ℕ) < 2 * (r + 1) := by
      have : (j : ℕ) ≤ r := Nat.lt_succ_iff.mp j.is_lt
      omega
    have hne : (r + 1) + (j : ℕ) ≠ 2 * (r + 1) := Nat.ne_of_lt hj
    simp only [c, d, if_neg hne]
  -- Locality forces equal outputs at `r+1`, but `lookahead` distinguishes them.
  have hstep : stepOf r g c (r + 1) = stepOf r g d (r + 1) :=
    stepOf_local r g c d (r + 1) hwin
  have hc_eval : lookahead c (r + 1) = (0 : Alph) := by simp [lookahead, c]
  have hd_eval : lookahead d (r + 1) = (1 : Alph) := by simp [lookahead, d]
  have : (0 : Alph) = 1 :=
    calc (0 : Alph) = lookahead c (r + 1) := hc_eval.symm
      _ = stepOf r g c (r + 1) := by rw [hF]
      _ = stepOf r g d (r + 1) := hstep
      _ = lookahead d (r + 1) := by rw [hF]
      _ = 1 := hd_eval
  exact absurd this (by decide)

/-- **The predicate is not universal.**  In stark contrast to
`dual_layer_universality` — where *every* self-map is a `step` — there exists a map
that is not a generation step.  So `IsGenerativeStep` genuinely partitions the space
of maps and can serve as evidence. -/
theorem generativeStep_not_universal : ¬ ∀ F : Config → Config, IsGenerativeStep F :=
  fun h => lookahead_not_generativeStep (h lookahead)

/-! ## Axiom audit -/

#print axioms lookahead_not_generativeStep
#print axioms generativeStep_not_universal
#print axioms id_isGenerativeStep

end Falsifiability
end Generative
end RGF
