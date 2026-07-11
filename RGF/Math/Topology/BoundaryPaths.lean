/-
  Construction and counting of boundary-crossing paths on discrete networks
  Construction and Counting of Boundary-Crossing Paths on Discrete Networks

  Reference paper: 70. Construction and counting of boundary-crossing paths on discrete networks
-/

import Mathlib
import RGF.Math.Graph.GraphAutomorphism
import RGF.Math.Graph.PetersenGraph

open Finset BigOperators SimpleGraph

/-- The number of walks of length k (defined via powers of the adjacency matrix). -/
noncomputable def walkCount {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) (u v : Fin n) : ℕ :=
  (G.adjMatrix ℕ ^ k) u v

/-- The Boolean version of the adjacency matrix. -/
def SimpleGraph.adjBoolMatrix {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if G.Adj i j then 1 else 0

/-- The number of boundary-crossing edges. -/
def crossingEdges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ (Finset.univ \ S)).filter (fun p => G.Adj p.1 p.2)).card

/-- The number of boundary-crossing edges is non-negative. -/
theorem crossingEdges_nonneg {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S : Finset (Fin n)) :
    0 ≤ crossingEdges G S := Nat.zero_le _

/-- The whole set has no boundary-crossing edges. -/
theorem crossingEdges_univ {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    crossingEdges G Finset.univ = 0 := by
  simp [crossingEdges]

/-- The empty set has no boundary-crossing edges. -/
theorem crossingEdges_empty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    crossingEdges G ∅ = 0 := by
  simp [crossingEdges]

/-
Handshake lemma: the sum of degrees = 2 × the number of edges
-/
theorem handshaking_lemma {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    ∑ v : Fin n, (G.neighborFinset v).card = 2 * G.edgeFinset.card := by
  convert G.sum_degrees_eq_twice_card_edges

/-- The number of crossing edges on C₅ for S = {0, 1}. -/
theorem c5_crossing_01 :
    crossingEdges c5Graph {0, 1} = 2 := by
  decide

/-- The number of crossing edges on K₅ for S = {0, 1}. -/
theorem k5_crossing_01 :
    crossingEdges (⊤ : SimpleGraph (Fin 5)) {0, 1} = 6 := by
  decide

/-- The number of crossing edges on the Petersen graph for the outer cycle. -/
theorem petersen_crossing_outer :
    crossingEdges petersenGraph {0, 1, 2, 3, 4} = 5 := by
  decide

/-- The manifestation of the quintic structure in boundary paths. -/
theorem five_in_boundary_paths :
    (crossingEdges petersenGraph {0, 1, 2, 3, 4} = 5) ∧
    (crossingEdges c5Graph {0, 1} = 2) ∧
    (crossingEdges (⊤ : SimpleGraph (Fin 5)) {0, 1} = 6) ∧
    (5 = Fintype.card (Fin 5)) := by
  refine ⟨by decide, by decide, by decide, by simp⟩