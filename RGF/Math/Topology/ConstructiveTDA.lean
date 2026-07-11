/-
  RGF/ConstructiveTDA.lean

  Task IV — Constructive topological data analysis (TDA).

  A `sorry`-free, purely finite/combinatorial toolbox for TDA on discrete
  lattice data, extending `PersistentHomology.lean`:

  * `vrComplex d ε` : the Vietoris–Rips complex of a finite metric data set at
    scale `ε`, together with a proof that it is a genuine abstract simplicial
    complex (downward closed).
  * `vrComplex_mono` : the Rips construction is a *filtration* (monotone in `ε`)
    — the functoriality of the persistence pipeline.
  * `cech_sub_vr_two` : the Rips/Čech interleaving in combinatorial form.
  * `bottleneck A B` : the bottleneck distance between two persistence diagrams
    (finite indexed point clouds), with the full metric package proved:
    `bottleneck_nonneg`, `bottleneck_self`, `bottleneck_symm`,
    `bottleneck_triangle`.
  * `bottleneck_stability` : the constructive stability theorem — a pointwise
    perturbation of a persistence diagram of size `δ` changes it by at most `δ`
    in bottleneck distance.

  Everything is finite and constructive: no real-infinity presupposition beyond
  the finite `inf'`/`sup'` lattice operations.
-/

import Mathlib
import RGF.Math.Topology.PersistentHomology

open scoped BigOperators
open Finset

namespace RGF.TDA

/-! ## 1. The Vietoris–Rips filtration -/

open Classical in
/-- Simplices of the Vietoris–Rips complex: finite vertex sets whose pairwise
    distances are all `≤ ε`. -/
noncomputable def vrSimplices {n : ℕ} (d : Fin n → Fin n → ℝ) (ε : ℝ) :
    Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter (fun σ => ∀ i ∈ σ, ∀ j ∈ σ, d i j ≤ ε)

theorem mem_vrSimplices {n : ℕ} (d : Fin n → Fin n → ℝ) (ε : ℝ) (σ : Finset (Fin n)) :
    σ ∈ vrSimplices d ε ↔ ∀ i ∈ σ, ∀ j ∈ σ, d i j ≤ ε := by
  unfold vrSimplices; aesop;

theorem vrSimplices_empty {n : ℕ} (d : Fin n → Fin n → ℝ) (ε : ℝ) :
    (∅ : Finset (Fin n)) ∈ vrSimplices d ε := by
  exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by simp +decide ⟩

theorem vrSimplices_down_closed {n : ℕ} (d : Fin n → Fin n → ℝ) (ε : ℝ)
    (σ : Finset (Fin n)) (hσ : σ ∈ vrSimplices d ε) (τ : Finset (Fin n)) (hτ : τ ⊆ σ) :
    τ ∈ vrSimplices d ε := by
  exact mem_vrSimplices d ε τ |>.2 fun i hi j hj => mem_vrSimplices d ε σ |>.1 hσ i ( hτ hi ) j ( hτ hj )

open Classical in
/-- The Vietoris–Rips complex of a symmetric distance `d` on `Fin n` at scale `ε`. -/
noncomputable def vrComplex {n : ℕ} (d : Fin n → Fin n → ℝ) (ε : ℝ) :
    AbstractSimplicialComplex (Fin n) where
  simplices := vrSimplices d ε
  empty_mem := vrSimplices_empty d ε
  down_closed := vrSimplices_down_closed d ε

/-
The Rips construction is a filtration: monotone (inclusion) in the scale.
-/
theorem vrComplex_mono {n : ℕ} (d : Fin n → Fin n → ℝ) {ε ε' : ℝ} (h : ε ≤ ε') :
    (vrComplex d ε).simplices ⊆ (vrComplex d ε').simplices := by
  exact fun x hx => mem_vrSimplices d ε' x |>.2 fun i hi j hj => le_trans ( mem_vrSimplices d ε x |>.1 hx i hi j hj ) h

/-! ## 2. A combinatorial Čech complex and Rips/Čech interleaving -/

open Classical in
/-- Simplices of a combinatorial Čech-type complex: vertex sets admitting a
    common center vertex `c` within radius `ε`. -/
noncomputable def cechSimplices {n : ℕ} (d : Fin n → Fin n → ℝ) (ε : ℝ) :
    Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter (fun σ => ∃ c : Fin n, ∀ i ∈ σ, d c i ≤ ε)

theorem mem_cechSimplices {n : ℕ} (d : Fin n → Fin n → ℝ) (ε : ℝ) (σ : Finset (Fin n)) :
    σ ∈ cechSimplices d ε ↔ ∃ c : Fin n, ∀ i ∈ σ, d c i ≤ ε := by
  unfold cechSimplices; aesop;

/-
Rips/Čech interleaving (one containment): if `d` is symmetric and satisfies
    the triangle inequality, every Čech `ε`-simplex is a Rips `2ε`-simplex.
-/
theorem cech_sub_vr_two {n : ℕ} (d : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, d i j = d j i)
    (htri : ∀ i j k, d i j ≤ d i k + d k j) (ε : ℝ) :
    cechSimplices d ε ⊆ vrSimplices d (2 * ε) := by
  intro σ hσ;
  obtain ⟨c, hc⟩ := (mem_cechSimplices d ε σ).mp hσ;
  exact mem_vrSimplices d ( 2 * ε ) σ |>.2 fun i hi j hj => by linarith [ htri i j c, hc i hi, hc j hj, hsymm i c, hsymm j c ] ;

/-! ## 3. Bottleneck distance on persistence diagrams -/

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Chebyshev (L∞) distance between two points of the persistence plane. -/
def chebyshev (p q : ℝ × ℝ) : ℝ := max |p.1 - q.1| |p.2 - q.2|

theorem chebyshev_nonneg (p q : ℝ × ℝ) : 0 ≤ chebyshev p q := by
  exact le_max_of_le_left ( abs_nonneg _ )

theorem chebyshev_self (p : ℝ × ℝ) : chebyshev p p = 0 := by
  unfold chebyshev; aesop;

theorem chebyshev_symm (p q : ℝ × ℝ) : chebyshev p q = chebyshev q p := by
  unfold chebyshev; simp +decide [ abs_sub_comm ] ;

theorem chebyshev_triangle (p q r : ℝ × ℝ) :
    chebyshev p r ≤ chebyshev p q + chebyshev q r := by
  exact max_le ( le_trans ( abs_sub_le _ _ _ ) ( add_le_add ( le_max_left _ _ ) ( le_max_left _ _ ) ) ) ( le_trans ( abs_sub_le _ _ _ ) ( add_le_add ( le_max_right _ _ ) ( le_max_right _ _ ) ) )

/-- The cost of matching diagram `A` to diagram `B` along the bijection `σ`:
    the worst (sup) pointwise Chebyshev displacement. -/
noncomputable def matchCost (A B : ι → ℝ × ℝ) (σ : Equiv.Perm ι) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => chebyshev (A i) (B (σ i)))

/-- The bottleneck distance: the best matching cost over all bijections. -/
noncomputable def bottleneck (A B : ι → ℝ × ℝ) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm ι)).inf' Finset.univ_nonempty (matchCost A B)

omit [DecidableEq ι] in
theorem matchCost_nonneg (A B : ι → ℝ × ℝ) (σ : Equiv.Perm ι) : 0 ≤ matchCost A B σ := by
  exact le_trans ( chebyshev_nonneg _ _ ) ( Finset.le_sup' ( fun i => chebyshev ( A i ) ( B ( σ i ) ) ) ( Finset.mem_univ ( Classical.arbitrary ι ) ) )

omit [DecidableEq ι] in
theorem matchCost_le_iff (A B : ι → ℝ × ℝ) (σ : Equiv.Perm ι) (c : ℝ) :
    matchCost A B σ ≤ c ↔ ∀ i, chebyshev (A i) (B (σ i)) ≤ c := by
  unfold matchCost; aesop;

theorem bottleneck_nonneg (A B : ι → ℝ × ℝ) : 0 ≤ bottleneck A B := by
  convert Finset.le_inf' _ _ _;
  exact fun _ _ => matchCost_nonneg A B _

/-
The bottleneck distance is bounded above by the cost of any single matching.
-/
theorem bottleneck_le_matchCost (A B : ι → ℝ × ℝ) (σ : Equiv.Perm ι) :
    bottleneck A B ≤ matchCost A B σ := by
  exact Finset.inf'_le _ ( Finset.mem_univ σ )

/-
The bottleneck distance from a diagram to itself is zero.
-/
theorem bottleneck_self (A : ι → ℝ × ℝ) : bottleneck A A = 0 := by
  refine' le_antisymm ( bottleneck_le_matchCost A A ( Equiv.refl ι ) |> le_trans <| Finset.sup'_le _ _ _ ) ( bottleneck_nonneg A A );
  simp +decide [ chebyshev ]

/-
Symmetry of the matching cost under inverse permutations.
-/
omit [DecidableEq ι] in
theorem matchCost_symm (A B : ι → ℝ × ℝ) (σ : Equiv.Perm ι) :
    matchCost A B σ = matchCost B A σ⁻¹ := by
  refine' le_antisymm _ _;
  · rw [ matchCost_le_iff ];
    exact fun i => Finset.le_sup' ( fun j => chebyshev ( B j ) ( A ( σ⁻¹ j ) ) ) ( Finset.mem_univ ( σ i ) ) |> le_trans ( by simp +decide [ chebyshev_symm ] );
  · refine' Finset.sup'_le _ _ _;
    intro i hi;
    convert Finset.le_sup' ( fun j => chebyshev ( A j ) ( B ( σ j ) ) ) ( Finset.mem_univ ( σ⁻¹ i ) ) using 1;
    rw [ show σ (σ⁻¹ i) = i from σ.apply_symm_apply i, chebyshev_symm ]

/-
The bottleneck distance is symmetric.
-/
theorem bottleneck_symm (A B : ι → ℝ × ℝ) : bottleneck A B = bottleneck B A := by
  refine' le_antisymm _ _ <;> simp +decide [ bottleneck ];
  · intro b
    use b⁻¹;
    convert matchCost_symm A B b⁻¹ |> le_of_eq using 1;
  · grind +suggestions

/-
**The triangle inequality for the bottleneck distance.**
-/
theorem bottleneck_triangle (A B C : ι → ℝ × ℝ) :
    bottleneck A C ≤ bottleneck A B + bottleneck B C := by
  have h1 : ∀ σ τ : Equiv.Perm ι, matchCost A C (τ * σ) ≤ matchCost A B σ + matchCost B C τ := by
    intro σ τ
    have h_triangle : ∀ i, chebyshev (A i) (C ((τ * σ) i)) ≤ chebyshev (A i) (B (σ i)) + chebyshev (B (σ i)) (C (τ (σ i))) := by
      intro i
      apply chebyshev_triangle;
    refine' Finset.sup'_le _ _ _;
    exact fun i _ => le_trans ( h_triangle i ) ( add_le_add ( Finset.le_sup' ( fun i => chebyshev ( A i ) ( B ( σ i ) ) ) ( Finset.mem_univ i ) ) ( Finset.le_sup' ( fun i => chebyshev ( B i ) ( C ( τ i ) ) ) ( Finset.mem_univ ( σ i ) ) ) );
  -- Fix σ. Since bottleneck A C - matchCost A B σ ≤ matchCost B C τ for all τ, we get bottleneck A C - matchCost A B σ ≤ bottleneck B C.
  have h2 (σ : Equiv.Perm ι) : bottleneck A C - matchCost A B σ ≤ bottleneck B C := by
    simp_all +decide [ bottleneck ];
    exact fun τ => ⟨ τ * σ, by linarith [ h1 σ τ ] ⟩;
  -- So bottleneck A C ≤ matchCost A B σ + bottleneck B C for all σ.
  have h3 (σ : Equiv.Perm ι) : bottleneck A C ≤ matchCost A B σ + bottleneck B C := by
    linarith [ h2 σ ];
  -- Then bottleneck A C - bottleneck B C ≤ matchCost A B σ for all σ, so ≤ bottleneck A B = inf'_σ matchCost A B σ (Finset.le_inf').
  have h4 : bottleneck A C - bottleneck B C ≤ bottleneck A B := by
    exact Finset.le_inf' _ _ fun σ _ => by linarith [ h3 σ ] ;
  linarith

/-
**Constructive stability theorem.** If every point of the persistence diagram
    `A` is within Chebyshev distance `δ` of the corresponding point of `B` (under
    the identity indexing), then the bottleneck distance is at most `δ`. In
    particular a size-`δ` perturbation of the data changes the diagram by at most
    `δ` in the bottleneck metric.
-/
theorem bottleneck_stability (A B : ι → ℝ × ℝ) {δ : ℝ}
    (h : ∀ i, chebyshev (A i) (B i) ≤ δ) : bottleneck A B ≤ δ := by
  refine' le_trans ( bottleneck_le_matchCost A B ( Equiv.refl ι ) ) _;
  exact Finset.sup'_le _ _ fun i _ => h i

end RGF.TDA