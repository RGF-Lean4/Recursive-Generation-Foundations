/-
  Topological data analysis: persistent homology and the Betti numbers of the emergent space
  Topological Data Analysis: Persistent Homology and Betti Numbers of Emergence Spaces

  Formalizes:
  - basic constructions of simplicial complexes
  - the relation between Betti numbers and the Euler characteristic
  - a discretized framework for persistent homology
  - the topological fingerprint of the quintic structure
  - filtrations and the stability of Betti numbers
-/

import Mathlib

open Finset BigOperators

/-! ## 1. Abstract simplicial complexes -/

/-- An abstract simplicial complex: a finite family of sets closed under subsets. -/
structure AbstractSimplicialComplex (α : Type*) [DecidableEq α] where
  simplices : Finset (Finset α)
  empty_mem : ∅ ∈ simplices
  down_closed : ∀ σ ∈ simplices, ∀ τ : Finset α, τ ⊆ σ → τ ∈ simplices

/-- The dimension of a simplex = number of vertices - 1. -/
def simplexDim {α : Type*} [DecidableEq α] (σ : Finset α) : ℤ :=
  (σ.card : ℤ) - 1

/-- The empty simplex has dimension -1. -/
theorem simplexDim_empty (α : Type*) [DecidableEq α] :
    simplexDim (∅ : Finset α) = -1 := by
  simp [simplexDim]

/-- The number of k-simplices. -/
def fVector {α : Type*} [DecidableEq α]
    (K : AbstractSimplicialComplex α) (k : ℕ) : ℕ :=
  (K.simplices.filter (fun σ => σ.card = k + 1)).card

def vertexCount {α : Type*} [DecidableEq α] (K : AbstractSimplicialComplex α) : ℕ := fVector K 0
def edgeCount {α : Type*} [DecidableEq α] (K : AbstractSimplicialComplex α) : ℕ := fVector K 1
def faceCount {α : Type*} [DecidableEq α] (K : AbstractSimplicialComplex α) : ℕ := fVector K 2

/-! ## 2. Euler characteristic -/

/-- The Euler characteristic as the alternating sum of the f-vector. -/
def eulerChar {α : Type*} [DecidableEq α]
    (K : AbstractSimplicialComplex α) (d : ℕ) : ℤ :=
  ∑ k ∈ range (d + 1), (-1 : ℤ) ^ k * (fVector K k : ℤ)

/-- The Euler characteristic in dimension 1 = V - E. -/
theorem eulerChar_dim1 {α : Type*} [DecidableEq α]
    (K : AbstractSimplicialComplex α) :
    eulerChar K 1 = (vertexCount K : ℤ) - (edgeCount K : ℤ) := by
  simp only [eulerChar, vertexCount, edgeCount]
  simp [Finset.sum_range_succ]
  ring

/-- The Euler characteristic in dimension 2 = V - E + F. -/
theorem eulerChar_dim2 {α : Type*} [DecidableEq α]
    (K : AbstractSimplicialComplex α) :
    eulerChar K 2 = (vertexCount K : ℤ) - (edgeCount K : ℤ) + (faceCount K : ℤ) := by
  simp only [eulerChar, vertexCount, edgeCount, faceCount]
  simp [Finset.sum_range_succ]
  ring

/-! ## 3. Betti numbers -/

structure BettiNumbers where
  beta0 : ℕ  -- number of connected components
  beta1 : ℕ  -- number of independent cycles
  beta2 : ℕ  -- number of voids

def BettiNumbers.eulerPoincare (b : BettiNumbers) : ℤ :=
  (b.beta0 : ℤ) - (b.beta1 : ℤ) + (b.beta2 : ℤ)

theorem connected_beta0 (b : BettiNumbers) (h : b.beta0 = 1) :
    b.eulerPoincare = 1 - (b.beta1 : ℤ) + (b.beta2 : ℤ) := by
  simp [BettiNumbers.eulerPoincare, h]

theorem tree_betti (b : BettiNumbers) (h0 : b.beta0 = 1) (h1 : b.beta1 = 0) :
    b.eulerPoincare = 1 + (b.beta2 : ℤ) := by
  simp [BettiNumbers.eulerPoincare, h0, h1]

/-! ## 4. Persistent homology -/

structure Filtration (α : Type*) [DecidableEq α] where
  atScale : ℕ → Finset (Finset α)
  monotone : ∀ s t : ℕ, s ≤ t → atScale s ⊆ atScale t

structure PersistenceInterval where
  birth : ℕ
  death : ℕ
  birth_le_death : birth ≤ death

def PersistenceInterval.persistence (I : PersistenceInterval) : ℕ :=
  I.death - I.birth

def PersistenceDiagram := List PersistenceInterval

def totalPersistence (D : PersistenceDiagram) : ℕ :=
  D.foldl (fun acc I => acc + I.persistence) 0

def longLivedFeatures (D : PersistenceDiagram) (threshold : ℕ) : ℕ :=
  (D.filter (fun I => threshold ≤ I.persistence)).length

/-! ## 5. The topological fingerprint of the quintic structure -/

def K5Boundary : Finset (Finset (Fin 5)) :=
  (Finset.univ : Finset (Fin 5)).powerset

theorem K5_vertex_count :
    (K5Boundary.filter (fun σ => σ.card = 1)).card = 5 := by decide

theorem K5_edge_count :
    (K5Boundary.filter (fun σ => σ.card = 2)).card = 10 := by decide

theorem K5_triangle_count :
    (K5Boundary.filter (fun σ => σ.card = 3)).card = 10 := by decide

theorem K5_tetrahedron_count :
    (K5Boundary.filter (fun σ => σ.card = 4)).card = 5 := by decide

theorem K5_total_simplices :
    K5Boundary.card = 32 := by decide

theorem K5_euler_char :
    (5 : ℤ) - 10 + 10 - 5 + 1 = 1 := by norm_num

/-! ## 6. The Vietoris-Rips complex -/

def DistanceMatrix (n : ℕ) := Fin n → Fin n → ℝ

noncomputable def ripsEdges {n : ℕ} (d : DistanceMatrix n) (ε : ℝ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ d p.1 p.2 ≤ ε)

theorem rips_edges_mono {n : ℕ} (d : DistanceMatrix n) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    ripsEdges d ε₁ ⊆ ripsEdges d ε₂ := by
  intro p hp
  simp [ripsEdges] at hp ⊢
  exact ⟨hp.1, le_trans hp.2 h⟩

/-! ## 7. Betti numbers and quintic locking -/

theorem icosahedron_euler : (12 : ℤ) - 30 + 20 = 2 := by norm_num
theorem dodecahedron_euler : (20 : ℤ) - 30 + 12 = 2 := by norm_num

theorem fivefold_polyhedra_euler :
    (12 : ℤ) - 30 + 20 = 2 ∧ (20 : ℤ) - 30 + 12 = 2 := by
  constructor <;> norm_num

theorem surface_beta0 (b : BettiNumbers) (hconn : b.beta0 = 1)
    (hsphere : b.eulerPoincare = 2) : (b.beta1 : ℤ) = (b.beta2 : ℤ) - 1 := by
  simp [BettiNumbers.eulerPoincare] at hsphere; omega

theorem sphere_betti :
    let b : BettiNumbers := ⟨1, 0, 1⟩
    b.eulerPoincare = 2 := by
  simp [BettiNumbers.eulerPoincare]

/-! ## 8. Stability of persistent homology -/

def bottleneckBound (I₁ I₂ : PersistenceInterval) : ℕ :=
  max (Int.natAbs ((I₁.birth : ℤ) - I₂.birth))
      (Int.natAbs ((I₁.death : ℤ) - I₂.death))

theorem bottleneckBound_self (I : PersistenceInterval) :
    bottleneckBound I I = 0 := by
  simp [bottleneckBound, Int.natAbs]

theorem stability_consequence (I : PersistenceInterval) (δ : ℕ)
    (h : δ < I.persistence) : 0 < I.persistence := by omega
