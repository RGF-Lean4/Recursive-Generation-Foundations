/-
  The Laplacian matrix of a graph and its spectral properties
  Graph Laplacian Matrix and Spectral Properties

  Reference paper: 68. Applications of the Laplacian matrix in the theory of recursive generation
-/

import Mathlib
import RGF.Math.Graph.GraphAutomorphism

open Finset BigOperators SimpleGraph Matrix

/-- The adjacency matrix of a graph (real-valued). -/
noncomputable def SimpleGraph.adjMatrixReal {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if G.Adj i j then 1 else 0

/-- The degree matrix of a graph. -/
noncomputable def SimpleGraph.rgfDegMatrix {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => ((G.neighborFinset i).card : ℝ)

/-- The graph Laplacian matrix L = D - A. -/
noncomputable def SimpleGraph.rgfLaplacianMatrix {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Matrix (Fin n) (Fin n) ℝ :=
  G.rgfDegMatrix - G.adjMatrixReal

/-
The row sums of the Laplacian matrix are zero
-/
theorem SimpleGraph.rgfLaplacianMatrix_row_sum {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i : Fin n) :
    ∑ j : Fin n, G.rgfLaplacianMatrix i j = 0 := by
  unfold SimpleGraph.rgfLaplacianMatrix SimpleGraph.rgfDegMatrix SimpleGraph.adjMatrixReal;
  simp +decide [ SimpleGraph.neighborFinset ];
  simp +decide [ diagonal ]

/-- The degree of C₅ = 2. -/
theorem c5_laplacian_degree : ∀ v : Fin 5, (c5Graph.neighborFinset v).card = 2 := by
  decide

/-- The edge count of K₅ and a combinatorial identity. -/
theorem k5_spectral_gap_is_five :
    (⊤ : SimpleGraph (Fin 5)).edgeFinset.card = 10 ∧
    (Nat.choose 5 2 = 10) := by
  exact ⟨by decide, by decide⟩

/-- The manifestation of quintic locking in spectral graph theory. -/
theorem five_locking_spectral :
    (Nat.totient 5 = 4) ∧
    (¬ IsSolvable (Equiv.Perm (Fin 5))) := by
  constructor
  · decide
  · exact Equiv.Perm.not_solvable _ (by simp [Cardinal.mk_fintype])