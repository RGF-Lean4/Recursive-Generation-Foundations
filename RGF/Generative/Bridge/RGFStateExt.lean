/-
  RGFStateExt.lean — directed-graph and hypergraph extensions of RGF states
  Directed Graph and Hypergraph Extensions of RGF States

  This file formalizes:
  1. directed-graph RGF states (dropping the symmetry requirement)
  2. hypergraph RGF states (edges may connect arbitrarily many vertices)
  3. graph-generation universality for the directed-graph and hypergraph versions
  4. the connection to undirected-graph RGF states
-/

import Mathlib

open Finset BigOperators

/-! ============================================================
    Preliminaries: reuse the dual-layer iteration system definition
    ============================================================ -/

/-- Abstract dual-layer iteration system. -/
structure RGFDualLayerExt (R E : Type*) where
  generate : R → E
  modify   : E → R

namespace RGFDualLayerExt

def step {R E : Type*} (sys : RGFDualLayerExt R E) (r : R) : R :=
  sys.modify (sys.generate r)

def IsFixedPoint {R E : Type*} (sys : RGFDualLayerExt R E) (r : R) : Prop :=
  sys.step r = r

def iterateN {R E : Type*} (sys : RGFDualLayerExt R E) : ℕ → R → R
  | 0, r => r
  | n + 1, r => sys.step (sys.iterateN n r)

end RGFDualLayerExt

/-! ============================================================
    Part 1: directed-graph RGF states
    ============================================================ -/

/-- Directed-graph RGF state: a directed adjacency relation on n nodes (no symmetry required, still loopless). -/
structure RGF_State_DiGraph (n : ℕ) where
  adj : Fin n → Fin n → Bool
  irrefl : ∀ i, adj i i = false

/-- Undirected-graph RGF state (restated, for comparison). -/
structure RGF_State_Graph (n : ℕ) where
  adj : Fin n → Fin n → Bool
  symm : ∀ i j, adj i j = adj j i
  irrefl : ∀ i, adj i i = false

/-- Encode Mathlib's Digraph as a directed-graph RGF state. -/
noncomputable def encode_digraph {n : ℕ} (D : Digraph (Fin n))
    [DecidableRel D.Adj] (hirr : ∀ i, ¬ D.Adj i i) : RGF_State_DiGraph n where
  adj := fun i j => decide (D.Adj i j)
  irrefl := by intro i; simp [hirr]

/-- Decode a directed-graph RGF state back into a Digraph. -/
def decode_digraph {n : ℕ} (s : RGF_State_DiGraph n) : Digraph (Fin n) where
  Adj := fun i j => s.adj i j = true

/-- Encode-decode consistency (directed-graph version). -/
theorem digraph_encode_decode_id {n : ℕ} (D : Digraph (Fin n))
    [DecidableRel D.Adj] (hirr : ∀ i, ¬ D.Adj i i) :
    decode_digraph (encode_digraph D hirr) = D := by
  ext i j; simp [decode_digraph, encode_digraph]

/-- An undirected graph can be embedded into a directed graph (symmetrization). -/
def undirected_to_directed {n : ℕ} (s : RGF_State_Graph n) : RGF_State_DiGraph n where
  adj := s.adj
  irrefl := s.irrefl

/-- The undirected embedding preserves the adjacency relation. -/
theorem undirected_embed_preserves {n : ℕ} (s : RGF_State_Graph n) :
    (undirected_to_directed s).adj = s.adj := rfl

/-- Decide whether a directed-graph state is undirected (symmetric). -/
def RGF_State_DiGraph.isSymmetric {n : ℕ} (s : RGF_State_DiGraph n) : Prop :=
  ∀ i j, s.adj i j = s.adj j i

/-- A symmetric directed-graph state can be converted into an undirected-graph state. -/
def symmetric_digraph_to_graph {n : ℕ} (s : RGF_State_DiGraph n)
    (hs : s.isSymmetric) : RGF_State_Graph n where
  adj := s.adj
  symm := hs
  irrefl := s.irrefl

/-! ### Universality of the directed-graph RGF system -/

/-- Construct a directed-graph-generating RGF system. -/
noncomputable def digraph_generating_system {n : ℕ} (D : Digraph (Fin n))
    [DecidableRel D.Adj] (hirr : ∀ i, ¬ D.Adj i i) :
    RGFDualLayerExt (RGF_State_DiGraph n) (RGF_State_DiGraph n) where
  generate := fun _ => encode_digraph D hirr
  modify := id

/-- The directed-graph encoding is a fixed point. -/
theorem digraph_encode_is_fixpoint {n : ℕ} (D : Digraph (Fin n))
    [DecidableRel D.Adj] (hirr : ∀ i, ¬ D.Adj i i) :
    (digraph_generating_system D hirr).IsFixedPoint (encode_digraph D hirr) := rfl

/-- Directed graph reached in one step. -/
theorem digraph_one_step_reach {n : ℕ} (D : Digraph (Fin n))
    [DecidableRel D.Adj] (hirr : ∀ i, ¬ D.Adj i i) (s₀ : RGF_State_DiGraph n) :
    (digraph_generating_system D hirr).step s₀ = encode_digraph D hirr := rfl

/-- **Theorem (universality of directed-graph generation)**:
    any finite directed graph can be generated in finitely many steps by some RGF dual-layer iteration system. -/
theorem rgf_digraph_universal {n : ℕ} (D : Digraph (Fin n))
    [DecidableRel D.Adj] (hirr : ∀ i, ¬ D.Adj i i) :
    ∃ (sys : RGFDualLayerExt (RGF_State_DiGraph n) (RGF_State_DiGraph n)),
      sys.IsFixedPoint (encode_digraph D hirr) ∧
      (∀ s₀, ∃ N, sys.iterateN N s₀ = encode_digraph D hirr) :=
  ⟨digraph_generating_system D hirr, digraph_encode_is_fixpoint D hirr,
   fun _ => ⟨1, rfl⟩⟩

/-! ============================================================
    Part 2: hypergraph RGF states
    ============================================================ -/

/-- Hypergraph RGF state: a set of hyperedges on n nodes.
    Each hyperedge is a Finset (Fin n) containing at least 2 vertices. -/
structure RGF_State_Hyper (n : ℕ) where
  edges : Finset (Finset (Fin n))
  edge_size : ∀ e ∈ edges, 2 ≤ e.card

/-- A simple graph can be embedded into a hypergraph (each edge regarded as a 2-element hyperedge). -/
noncomputable def graph_to_hypergraph {n : ℕ} (s : RGF_State_Graph n) :
    RGF_State_Hyper n where
  edges := Finset.univ.filter (fun (e : Finset (Fin n)) =>
    e.card = 2 ∧ ∃ i j, i ∈ e ∧ j ∈ e ∧ i ≠ j ∧ s.adj i j = true)
  edge_size := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    omega

/-- Hypergraph automorphism: a permutation preserving the set of hyperedges. -/
structure HypergraphAutomorphism {n : ℕ} (H : RGF_State_Hyper n) where
  perm : Equiv.Perm (Fin n)
  preserves : ∀ e ∈ H.edges, e.map perm.toEmbedding ∈ H.edges

/-- Construct a hypergraph-generating RGF system. -/
noncomputable def hyper_generating_system {n : ℕ}
    (H : RGF_State_Hyper n) :
    RGFDualLayerExt (RGF_State_Hyper n) (RGF_State_Hyper n) where
  generate := fun _ => H
  modify := id

/-- The hypergraph encoding is a fixed point. -/
theorem hyper_encode_is_fixpoint {n : ℕ} (H : RGF_State_Hyper n) :
    (hyper_generating_system H).IsFixedPoint H := rfl

/-- **Theorem (universality of hypergraph generation)**:
    any finite hypergraph can be generated in finitely many steps by some RGF dual-layer iteration system. -/
theorem rgf_hyper_universal {n : ℕ} (H : RGF_State_Hyper n) :
    ∃ (sys : RGFDualLayerExt (RGF_State_Hyper n) (RGF_State_Hyper n)),
      sys.IsFixedPoint H ∧
      (∀ s₀, ∃ N, sys.iterateN N s₀ = H) :=
  ⟨hyper_generating_system H, hyper_encode_is_fixpoint H, fun _ => ⟨1, rfl⟩⟩

/-! ============================================================
    Part 3: directed-graph automorphism group
    ============================================================ -/

/-- Directed-graph automorphism: a permutation preserving the directed adjacency relation. -/
structure DiGraphAutomorphism {n : ℕ} (s : RGF_State_DiGraph n) where
  perm : Equiv.Perm (Fin n)
  preserves : ∀ i j, s.adj (perm i) (perm j) = s.adj i j

/-- The identity map is a directed-graph automorphism. -/
def DiGraphAutomorphism.id {n : ℕ} (s : RGF_State_DiGraph n) :
    DiGraphAutomorphism s where
  perm := Equiv.refl _
  preserves := fun _ _ => rfl

/-- Composition of directed-graph automorphisms. -/
def DiGraphAutomorphism.comp {n : ℕ} {s : RGF_State_DiGraph n}
    (σ τ : DiGraphAutomorphism s) : DiGraphAutomorphism s where
  perm := σ.perm.trans τ.perm
  preserves := by
    intro i j
    simp [Equiv.trans_apply]
    rw [τ.preserves, σ.preserves]

/-- Inverse of a directed-graph automorphism. -/
def DiGraphAutomorphism.inv {n : ℕ} {s : RGF_State_DiGraph n}
    (σ : DiGraphAutomorphism s) : DiGraphAutomorphism s where
  perm := σ.perm.symm
  preserves := by
    intro i j
    have h := σ.preserves (σ.perm.symm i) (σ.perm.symm j)
    simp at h; exact h.symm

/-! ============================================================
    Part 4: extension of the undirected-graph automorphism group by directed graphs
    ============================================================

    The automorphism group of a directed graph is generally a subgroup of the automorphism group of an undirected graph.
    This means orientation can "reduce the symmetry", making the
    construction in Frucht's theorem more flexible.
-/

/-- Undirected-graph automorphism (reused definition). -/
structure GraphAutomorphism {n : ℕ} (s : RGF_State_Graph n) where
  perm : Equiv.Perm (Fin n)
  preserves : ∀ i j, s.adj (perm i) (perm j) = s.adj i j

/-- A directed-graph automorphism of an undirected graph is also an undirected-graph automorphism. -/
def digraph_aut_of_undirected {n : ℕ} (s : RGF_State_Graph n)
    (σ : DiGraphAutomorphism (undirected_to_directed s)) :
    GraphAutomorphism s where
  perm := σ.perm
  preserves := σ.preserves

/-! ============================================================
    Part 5: combined theorem — unified RGF universality for directed graphs and hypergraphs
    ============================================================ -/

/-- **Combined theorem: the RGF framework uniformly covers undirected graphs, directed graphs, and hypergraphs.** -/
theorem rgf_extended_universality :
    -- (1) undirected-graph universality
    (∀ (n : ℕ) (s : RGF_State_Graph n),
      ∃ sys : RGFDualLayerExt (RGF_State_Graph n) (RGF_State_Graph n),
        sys.IsFixedPoint s) ∧
    -- (2) directed-graph universality
    (∀ (n : ℕ) (D : Digraph (Fin n)) [DecidableRel D.Adj],
      ∀ (hirr : ∀ i, ¬ D.Adj i i),
      ∃ sys : RGFDualLayerExt (RGF_State_DiGraph n) (RGF_State_DiGraph n),
        sys.IsFixedPoint (encode_digraph D hirr)) ∧
    -- (3) hypergraph universality
    (∀ (n : ℕ) (H : RGF_State_Hyper n),
      ∃ sys : RGFDualLayerExt (RGF_State_Hyper n) (RGF_State_Hyper n),
        sys.IsFixedPoint H) ∧
    -- (4) undirected graph embeds into directed graph
    (∀ (n : ℕ) (s : RGF_State_Graph n),
      ∃ d : RGF_State_DiGraph n, d.isSymmetric ∧ d.adj = s.adj) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n s; exact ⟨⟨fun _ => s, id⟩, rfl⟩
  · intro n D _ hirr; exact ⟨digraph_generating_system D hirr, digraph_encode_is_fixpoint D hirr⟩
  · intro n H; exact ⟨hyper_generating_system H, hyper_encode_is_fixpoint H⟩
  · intro n s; exact ⟨undirected_to_directed s, s.symm, rfl⟩

/-! ============================================================
    Axiom audit
    ============================================================ -/

#print axioms digraph_encode_decode_id
#print axioms rgf_digraph_universal
#print axioms rgf_hyper_universal
#print axioms rgf_extended_universality
