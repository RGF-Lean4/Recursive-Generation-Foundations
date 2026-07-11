/-
  Layer two: Turán graphs and extremal graph theory
  Recursive Generation Foundations (RGF)
-/

import Mathlib

open Finset BigOperators

/-- Turán graph: edges are drawn between vertices of different parts. -/
def turanGraph (n r : ℕ) (_hr : 0 < r) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u.val % r ≠ v.val % r
  symm _ _ := fun ⟨hne, hp⟩ => ⟨hne.symm, hp.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance turanDecAdj (n r : ℕ) (hr : 0 < r) : DecidableRel (turanGraph n r hr).Adj :=
  fun _ _ => instDecidableAnd

def turanEdgeCount (n r : ℕ) (hr : 0 < r) : ℕ :=
  (turanGraph n r hr).edgeFinset.card

theorem turan_4_2 : turanEdgeCount 4 2 (by omega) = 4 := by decide
theorem turan_5_2 : turanEdgeCount 5 2 (by omega) = 6 := by decide
theorem turan_6_3 : turanEdgeCount 6 3 (by omega) = 12 := by decide
theorem turan_5_5 : turanEdgeCount 5 5 (by omega) = 10 := by decide
theorem turan_10_5 : turanEdgeCount 10 5 (by omega) = 40 := by decide

theorem turanGraph_no_edge_same_part (n r : ℕ) (hr : 0 < r)
    (u v : Fin n) (h : u.val % r = v.val % r) :
    ¬(turanGraph n r hr).Adj u v :=
  fun ⟨_, hp⟩ => hp h

theorem turanGraph_cliqueFree (n r : ℕ) (hr : 1 ≤ r) :
    (turanGraph n r (by omega)).CliqueFree (r + 1) := by
  intro T hT;
  -- By the pigeonhole principle, since there are $r+1$ vertices and only $r$ possible residues modulo $r$, at least two vertices in $T$ must share the same residue modulo $r$.
  have h_pigeonhole : ∃ u v : Fin n, u ∈ T ∧ v ∈ T ∧ u ≠ v ∧ u.val % r = v.val % r := by
    by_contra! h;
    exact absurd ( Finset.card_le_card ( show Finset.image ( fun u : Fin n => ( u : ℕ ) % r ) T ⊆ Finset.range r from Finset.image_subset_iff.2 fun u hu => Finset.mem_range.2 <| Nat.mod_lt _ hr ) ) ( by rw [ Finset.card_image_of_injOn fun u hu v hv huv => by contrapose! huv; exact h u v hu hv huv ] ; simp +arith +decide [ hT.2 ] );
  obtain ⟨ u, v, hu, hv, huv, h ⟩ := h_pigeonhole; have := hT.1 hu hv; simp_all +decide [ turanGraph ] ;

/-- The project's definition of the Turán graph agrees with the edge set of `SimpleGraph.turanGraph` in Mathlib. -/
lemma turanEdgeCount_eq_mathlib (n r : ℕ) (hr : 0 < r) :
    turanEdgeCount n r hr = (SimpleGraph.turanGraph n r).edgeFinset.card := by
  unfold turanEdgeCount
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
  induction e using Sym2.ind with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeSet, turanGraph, SimpleGraph.turanGraph_adj]
    constructor
    · exact fun ⟨_, h⟩ => h
    · intro h; exact ⟨fun heq => by subst heq; exact h rfl, h⟩

theorem turan_theorem (n r : ℕ) (hr : 1 ≤ r) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.CliqueFree (r + 1)) :
    G.edgeFinset.card ≤ turanEdgeCount n r (by omega) := by
  rw [turanEdgeCount_eq_mathlib]
  exact (SimpleGraph.isTuranMaximal_turanGraph (by omega : 0 < r)).2 hG

theorem turan_5_symmetry :
    (Nat.factorial 2)^5 * Nat.factorial 5 = 3840 := by decide

theorem turan_5_dominates :
    turanEdgeCount 10 5 (by omega) > turanEdgeCount 10 4 (by omega) ∧
    turanEdgeCount 10 4 (by omega) > turanEdgeCount 10 3 (by omega) := by
  constructor <;> decide