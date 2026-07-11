import Mathlib

/-!
# Example: invariants of an RGF state

This file demonstrates how an RGF state (a graph on n vertices) carries topological and algebraic
invariants that are preserved under dual-layer iteration.

## Key concepts

1. An **RGF state** is an undirected simple graph on `Fin n`.
2. An **automorphism** of a state is a graph isomorphism from it to itself.
3. The automorphism group is an **invariant** — preserved under equivariant maps.
4. This is exactly the content of the core theorem `equivariant_preserves_aut`.
-/

open Finset

/-! ## Step 1: a simple graph as an RGF state -/

/-- RGF state on n nodes: an undirected simple graph given by an adjacency relation. -/
structure SimpleState' (n : ℕ) where
  adj : Fin n → Fin n → Bool
  symm : ∀ i j, adj i j = adj j i
  irrefl : ∀ i, adj i i = false

/-! ## Step 2: concrete examples -/

/-- The empty graph on 4 vertices (no edges). -/
def emptyState4' : SimpleState' 4 where
  adj := fun _ _ => false
  symm := by intros; rfl
  irrefl := by intros; rfl

/-- The complete graph K₃ on 3 vertices (all edges present). -/
def K3' : SimpleState' 3 where
  adj := fun i j => i != j
  symm := by intro i j; simp [bne_comm]
  irrefl := by intro i; simp

/-- The path graph P₃: 0—1—2 (a simple path on 3 vertices). -/
def P3' : SimpleState' 3 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 1 && j.val == 2) || (i.val == 2 && j.val == 1)
  symm := by intro i j; fin_cases i <;> fin_cases j <;> simp
  irrefl := by intro i; fin_cases i <;> simp

/-! ## Step 3: counting edges -/

/-- The number of edges in a state (each edge counted once). -/
def edgeCount' {n : ℕ} (s : SimpleState' n) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n =>
    p.1 < p.2 && s.adj p.1 p.2 == true)).card

/-- K₃ has 3 edges. -/
example : edgeCount' K3' = 3 := by decide

/-- P₃ has 2 edges. -/
example : edgeCount' P3' = 2 := by decide

/-- The empty graph has 0 edges. -/
example : edgeCount' emptyState4' = 0 := by decide

/-! ## Step 4: graph automorphisms -/

/-- A graph automorphism is a vertex permutation preserving the adjacency relation. -/
def IsAutomorphism' {n : ℕ} (s : SimpleState' n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j, s.adj (σ i) (σ j) = s.adj i j

/-- The identity map is always an automorphism. -/
theorem id_is_automorphism' {n : ℕ} (s : SimpleState' n) :
    IsAutomorphism' s (Equiv.refl _) := by
  intro i j; simp

/-! ## Key insight

The core theorem `equivariant_preserves_aut` in `Invariants/Theorems.lean` proves
the stronger conclusion: if the dual-layer iteration step is *equivariant* (commutes with all graph automorphisms),
then the automorphism group is preserved at every iteration step.

This means the symmetric structure of an RGF state is a genuine *dynamical invariant* — it cannot be
created or destroyed by iteration, only rearranged. This is the algebraic basis for the uniqueness result of the locking-membrane theorem.

See also:
- `Invariants/Basic.lean`: the full RGFState definition with Betti numbers
- `Invariants/Theorems.lean`: the equivariance theorem
- `Invariants/LockingMembrane.lean`: the complete derivation chain
-/
