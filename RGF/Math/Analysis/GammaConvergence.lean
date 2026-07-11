import Mathlib

/-!
# A self-contained theory of (sequential) Γ-convergence

Mathlib does not (yet) contain a development of De Giorgi's Γ-convergence.  This
file builds the part of the theory that the FORS "energy functional emergence"
argument needs, working with `EReal`-valued functionals on an arbitrary
topological space so that `liminf`/`limsup` are always well defined (`EReal` is a
complete linear order with the order topology).

The macroscopic ("emergent") energy functional of the FORS layer is obtained as a
**Γ-limit** of a sequence of microscopic (discrete) functionals.  The two facts
that make Γ-convergence *the* right notion for "emergence" are proved here in full
generality:

* `gammaConverges_unique` — the Γ-limit, when it exists, is **unique**;
* `gamma_fundamental` — the **fundamental theorem of Γ-convergence**: if the
  microscopic minimizers converge, their limit is a minimizer of the Γ-limit and
  the microscopic minimum *values* converge to it.

The downstream file `FORS/EnergyEmergence.lean` instantiates this with an explicit
discrete→continuum scaling sequence whose Γ-limit is the FORS geometric
dimension-reduction energy `(d − 2)²`, so that the locked membrane dimension
`d = 2` emerges as the unique Γ-limit minimizer.
-/

namespace RGF.Gamma

open Filter Topology

variable {X : Type*} [TopologicalSpace X]

/-- **Γ-liminf (lower bound) condition.**  For every point `x` and every sequence
`u n → x`, the limit functional is below the `liminf` of the discrete energies. -/
def GammaLiminf (F : ℕ → X → EReal) (Finf : X → EReal) : Prop :=
  ∀ x : X, ∀ u : ℕ → X, Tendsto u atTop (𝓝 x) →
    Finf x ≤ liminf (fun n => F n (u n)) atTop

/-- **Γ-limsup (recovery sequence) condition.**  For every point `x` there is a
"recovery" sequence `u n → x` along which the discrete energies do not exceed the
limit functional in the `limsup`. -/
def GammaLimsup (F : ℕ → X → EReal) (Finf : X → EReal) : Prop :=
  ∀ x : X, ∃ u : ℕ → X, Tendsto u atTop (𝓝 x) ∧
    limsup (fun n => F n (u n)) atTop ≤ Finf x

/-- **Sequential Γ-convergence** `F n ⟶Γ Finf`: both the liminf lower bound and the
existence of recovery sequences hold. -/
def GammaConverges (F : ℕ → X → EReal) (Finf : X → EReal) : Prop :=
  GammaLiminf F Finf ∧ GammaLimsup F Finf

/-- `x` is a (global) minimizer of an `EReal`-valued functional `G`. -/
def IsMinimizer (G : X → EReal) (x : X) : Prop := ∀ y : X, G x ≤ G y

/-- **Uniqueness of the Γ-limit.**  If a single sequence `F` Γ-converges to both
`Finf` and `Ginf`, they coincide. -/
theorem gammaConverges_unique {F : ℕ → X → EReal} {Finf Ginf : X → EReal}
    (hF : GammaConverges F Finf) (hG : GammaConverges F Ginf) : Finf = Ginf := by
  apply funext;
  intro x
  apply le_antisymm;
  · exact hG.2 x |> fun ⟨ u, hu, hlim ⟩ => hF.1 x u hu |> le_trans <| hlim.trans' <| liminf_le_limsup;
  · obtain ⟨ u, hu, h ⟩ := hF.2 x;
    exact le_trans ( hG.1 x u hu ) ( le_trans ( Filter.liminf_le_limsup ) h )

/-- **Fundamental theorem of Γ-convergence (convergence of minimizers).**
If `F n ⟶Γ Finf`, the sequence `u n` minimizes `F n` for each `n`, and `u n → x`,
then `x` minimizes `Finf` and the minimum *values* `F n (u n)` converge to
`Finf x` (the emergent minimum). -/
theorem gamma_fundamental
    {F : ℕ → X → EReal} {Finf : X → EReal} (h : GammaConverges F Finf)
    {u : ℕ → X} {x : X} (hu : Tendsto u atTop (𝓝 x))
    (hmin : ∀ n, ∀ z : X, F n (u n) ≤ F n z) :
    IsMinimizer Finf x ∧ Tendsto (fun n => F n (u n)) atTop (𝓝 (Finf x)) := by
  -- The microscopic minimum value sequence.
  set a : ℕ → EReal := fun n => F n (u n)
  -- Lower bound from the Γ-liminf condition.
  have hlb : Finf x ≤ liminf a atTop := h.1 x u hu
  -- Upper bound: for every `y`, `limsup a ≤ Finf y` (compare with a recovery sequence for `y`).
  have hub : ∀ y : X, limsup a atTop ≤ Finf y := by
    intro y
    obtain ⟨v, hv, hlimv⟩ := h.2 y
    calc limsup a atTop
        ≤ limsup (fun n => F n (v n)) atTop :=
          limsup_le_limsup (Eventually.of_forall fun n => hmin n (v n))
      _ ≤ Finf y := hlimv
  refine ⟨fun y => ?_, ?_⟩
  · calc Finf x ≤ liminf a atTop := hlb
      _ ≤ limsup a atTop := liminf_le_limsup
      _ ≤ Finf y := hub y
  · have hsup : limsup a atTop = Finf x :=
      le_antisymm (hub x) (le_trans hlb liminf_le_limsup)
    have hinf : liminf a atTop = Finf x :=
      le_antisymm (le_trans liminf_le_limsup (hub x)) hlb
    exact tendsto_of_liminf_eq_limsup hinf hsup

/-- A continuous real functional, regarded as a constant sequence of `EReal`
functionals, Γ-converges to itself.  (The constant continuous functional is its
own Γ-limit; this is the simplest "emergence" instance.) -/
theorem gammaConverges_const_of_continuous {g : X → ℝ} (hg : Continuous g) :
    GammaConverges (fun _ x => (g x : EReal)) (fun x => (g x : EReal)) := by
  constructor;
  · intro x u hu;
    have h_liminf : Filter.Tendsto (fun n => (g (u n) : EReal)) Filter.atTop (nhds (g x)) := by
      exact EReal.tendsto_coe.mpr ( hg.continuousAt.tendsto.comp hu );
    rw [ h_liminf.liminf_eq ];
  · intro x;
    refine' ⟨ fun _ => x, tendsto_const_nhds, _ ⟩ ; simp +decide

end RGF.Gamma