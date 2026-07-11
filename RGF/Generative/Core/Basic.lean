/-
  Invariants/Basic.lean — Shared foundation for the RGF invariant theory

  This is the common base file imported by the rest of the `Invariants.*`
  hierarchy (and, transitively, by `Category.RGF_Category`,
  `ExclusionProcess.KPZEmergence`, `ComplexNecessity`, …).

  It collects the core objects on which the invariant theory is built:

  * `RGFState n` — a (finite, undirected, loopless) RGF state on `n` vertices,
    recorded as a symmetric irreflexive boolean adjacency relation.
  * `RGFState.IsAut`, `RGFState.autGroup`, `RGFState.autOrder` — the symmetry
    (automorphism) data of a state.
  * the graph invariants `edges`/`edgeCount`, `triangles`/`triangleCount`,
    `betti0`, `betti1`, `eulerChar1` and the associated `toSimpleGraph`.
  * `RGFState.RGFMorphism` — an isomorphism (relabelling) between two states.
  * `RGFIterSystem n` — an iteration system together with its notion of a fixed
    point, the abstract dynamical layer used downstream.
-/

import Mathlib

open Finset BigOperators

/-- An RGF state on `n` vertices: a finite, undirected, loopless graph recorded
    as a symmetric irreflexive boolean adjacency relation. -/
structure RGFState (n : ℕ) where
  /-- The (boolean) adjacency relation. -/
  adj : Fin n → Fin n → Bool
  /-- Adjacency is symmetric (the graph is undirected). -/
  symm : ∀ i j, adj i j = adj j i
  /-- Adjacency is irreflexive (the graph is loopless). -/
  irrefl : ∀ i, adj i i = false

namespace RGFState

variable {n : ℕ}

/-! ### Automorphisms -/

/-- `σ` is an automorphism of the state `s` if relabelling by `σ` preserves
    adjacency. -/
def IsAut (s : RGFState n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j, s.adj (σ i) (σ j) = s.adj i j

/-- `IsAut` is decidable: it is a finite conjunction of boolean equalities. -/
instance instDecidableIsAut (s : RGFState n) (σ : Equiv.Perm (Fin n)) :
    Decidable (s.IsAut σ) := by
  unfold IsAut; infer_instance

/-- The identity permutation is an automorphism. -/
theorem id_is_aut (s : RGFState n) : s.IsAut 1 := by
  intro i j; simp [Equiv.Perm.one_apply]

/-- The composition of two automorphisms is an automorphism. -/
theorem aut_comp (s : RGFState n) (σ τ : Equiv.Perm (Fin n))
    (hσ : s.IsAut σ) (hτ : s.IsAut τ) : s.IsAut (σ * τ) := by
  intro i j; simp only [IsAut, Equiv.Perm.mul_apply] at *; rw [hσ, hτ]

/-- The inverse of an automorphism is an automorphism. -/
theorem inv_is_aut (s : RGFState n) (σ : Equiv.Perm (Fin n)) (hσ : s.IsAut σ) :
    s.IsAut σ⁻¹ := by
  intro i j; have := hσ (σ⁻¹ i) (σ⁻¹ j); simpa using this.symm

/-- The automorphism group of a state. -/
def autGroup (s : RGFState n) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | s.IsAut σ}
  one_mem' := s.id_is_aut
  mul_mem' := fun hσ hτ => s.aut_comp _ _ hσ hτ
  inv_mem' := fun hσ => s.inv_is_aut _ hσ

/-- The identity always lies in the automorphism group. -/
theorem autGroup_nonempty (s : RGFState n) : (1 : Equiv.Perm (Fin n)) ∈ s.autGroup :=
  s.id_is_aut

/-- The order (cardinality) of the automorphism group. -/
noncomputable def autOrder (s : RGFState n) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin n) // s.IsAut σ}

/-! ### The underlying simple graph -/

/-- The adjacency relation as a `Prop`-valued relation. -/
def AdjRel (s : RGFState n) (i j : Fin n) : Prop := s.adj i j

/-- The simple graph underlying an RGF state. -/
def toSimpleGraph (s : RGFState n) : SimpleGraph (Fin n) where
  Adj := s.AdjRel
  symm := by intro i j h; simp only [AdjRel] at *; rw [s.symm]; exact h
  loopless := ⟨by intro i h; simp [AdjRel, s.irrefl] at h⟩

/-- Adjacency of the underlying simple graph is decidable (it is a boolean test). -/
instance instDecidableAdjRel (s : RGFState n) : DecidableRel s.AdjRel := by
  intro i j; unfold AdjRel; infer_instance

/-- Adjacency of `toSimpleGraph` is decidable. -/
instance instDecidableToSimpleGraphAdj (s : RGFState n) :
    DecidableRel s.toSimpleGraph.Adj :=
  s.instDecidableAdjRel

/-- The number of connected components (zeroth Betti number). -/
noncomputable def betti0 (s : RGFState n) : ℕ :=
  Nat.card s.toSimpleGraph.ConnectedComponent

/-! ### Combinatorial invariants -/

open Classical in
/-- The set of (ordered, `i < j`) edges of the state. -/
noncomputable def edges (s : RGFState n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => s.adj p.1 p.2 ∧ p.1 < p.2)

/-- The number of edges. -/
noncomputable def edgeCount (s : RGFState n) : ℕ := s.edges.card

open Classical in
/-- The set of (ordered, `i < j < k`) triangles of the state. -/
noncomputable def triangles (s : RGFState n) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
    s.adj t.1 t.2.1 ∧ s.adj t.1 t.2.2 ∧ s.adj t.2.1 t.2.2)

/-- The number of triangles. -/
noncomputable def triangleCount (s : RGFState n) : ℕ := s.triangles.card

/-- An Euler-characteristic-style invariant `V - E + (triangles)`. -/
noncomputable def eulerChar1 (s : RGFState n) : ℤ :=
  (n : ℤ) - s.edgeCount + s.triangleCount

/-- The first Betti number `E - V + β₀`. -/
noncomputable def betti1 (s : RGFState n) : ℤ :=
  (s.edgeCount : ℤ) - n + s.betti0

/-! ### Morphisms -/

/-- An isomorphism (adjacency-preserving relabelling) between two RGF states. -/
structure RGFMorphism (s₁ s₂ : RGFState n) where
  /-- The underlying permutation of vertices. -/
  toEquiv : Equiv.Perm (Fin n)
  /-- The permutation carries the adjacency of `s₁` to that of `s₂`. -/
  preserves : ∀ i j, s₂.adj (toEquiv i) (toEquiv j) = s₁.adj i j

end RGFState

/-! ### The abstract dynamical (iteration) layer -/

/-- An RGF iteration system: a one-step evolution map on states. -/
structure RGFIterSystem (n : ℕ) where
  /-- One iteration step. -/
  step : RGFState n → RGFState n

namespace RGFIterSystem

variable {n : ℕ}

/-- A state is a fixed point if one step leaves it unchanged. -/
def IsFixedPoint (sys : RGFIterSystem n) (s : RGFState n) : Prop := sys.step s = s

end RGFIterSystem
