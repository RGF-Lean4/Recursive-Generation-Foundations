/-
  General Frucht theorem (labeled-directed-graph version)
  General Frucht Theorem (Labeled Directed Graph Version)

  Proof: any finite group G is isomorphic to the automorphism group of some labeled directed graph.

  Core idea: the Cayley labeled directed graph
  - vertex set = G
  - edge label label(x, y) = x⁻¹ * y (the group element by which to right-multiply to go from x to y)
  - a label-preserving permutation σ satisfies (σ x)⁻¹ * (σ y) = x⁻¹ * y
  - setting x = 1 gives σ(y) = σ(1) * y, i.e. σ is left multiplication
  - hence Aut ≅ G
-/

import Mathlib

open Equiv MulAction

/-! ============================================================
    Part 1: definition of a labeled directed graph
    ============================================================ -/

/-- A labeled directed graph: the complete directed graph on a vertex set V, each edge carrying a label from the label type L. -/
structure LabeledDigraph (V : Type*) (L : Type*) where
  /-- The edge-label function: the label of the edge from vertex x to vertex y. -/
  label : V → V → L

/-- An automorphism of a labeled directed graph: a vertex permutation preserving all edge labels. -/
def LabeledDigraph.IsAut {V L : Type*} (D : LabeledDigraph V L) (σ : Equiv.Perm V) : Prop :=
  ∀ x y : V, D.label (σ x) (σ y) = D.label x y

/-! ============================================================
    Part 2: the automorphism group as a Subgroup
    ============================================================ -/

/-- The automorphism group of a labeled directed graph. -/
def LabeledDigraph.autSubgroup {V L : Type*} (D : LabeledDigraph V L) :
    Subgroup (Equiv.Perm V) where
  carrier := {σ | D.IsAut σ}
  one_mem' := by
    intro x y
    simp [Equiv.Perm.one_apply]
  mul_mem' := by
    intro σ τ hσ hτ x y
    simp only [Set.mem_setOf_eq, IsAut] at *
    simp only [Equiv.Perm.mul_apply]
    rw [hσ, hτ]
  inv_mem' := by
    intro σ hσ x y
    simp only [Set.mem_setOf_eq, IsAut] at *
    have h := hσ (σ⁻¹ x) (σ⁻¹ y)
    simp at h
    exact h.symm

/-! ============================================================
    Part 3: the Cayley labeled directed graph
    ============================================================ -/

/-- The Cayley labeled directed graph: the complete labeled directed graph on a group G,
    with edge label label(x, y) = x⁻¹ * y. -/
def cayleyLabeledDigraph (G : Type*) [Group G] : LabeledDigraph G G where
  label x y := x⁻¹ * y

/-! ============================================================
    Part 4: left multiplication is an automorphism
    ============================================================ -/

/-
Left multiplication preserves the Cayley labels: (hx)⁻¹(hy) = x⁻¹h⁻¹hy = x⁻¹y
-/
theorem leftMul_isAut (G : Type*) [Group G]
    (h : G) : (cayleyLabeledDigraph G).IsAut (MulAction.toPerm (α := G) (β := G) h) := by
  unfold cayleyLabeledDigraph;
  intro x y; simp +decide [ mul_assoc ] ;

/-! ============================================================
    Part 5: every automorphism is a left multiplication (key lemma)
    ============================================================ -/

/-
Key lemma: any automorphism σ of the Cayley labeled directed graph satisfies σ(x) = σ(1) * x
-/
theorem aut_eq_leftMul_of_cayley {G : Type*} [Group G]
    (σ : Equiv.Perm G) (hσ : (cayleyLabeledDigraph G).IsAut σ) :
    ∀ x : G, σ x = σ 1 * x := by
  intro x
  have h := hσ 1 x
  simp [cayleyLabeledDigraph] at h
  exact (by
  rw [ ← h, mul_inv_cancel_left ];
  rw [ h ])

/-
Corollary: every automorphism equals some left-multiplication permutation
-/
theorem aut_is_leftMul {G : Type*} [Group G]
    (σ : Equiv.Perm G) (hσ : (cayleyLabeledDigraph G).IsAut σ) :
    σ = MulAction.toPerm (α := G) (β := G) (σ 1) := by
  convert aut_eq_leftMul_of_cayley σ hσ;
  simp +decide [Equiv.Perm.ext_iff]

/-! ============================================================
    Part 6: the core isomorphism theorem
    ============================================================ -/

/-
Multiplicative compatibility of eval₁: for automorphisms σ, τ,
    (σ * τ)(1) = σ(τ(1)) = σ(1) * τ(1)
-/
theorem evalOne_mul_compat {G : Type*} [Group G]
    (σ τ : (cayleyLabeledDigraph G).autSubgroup) :
    ((σ * τ : Equiv.Perm G) : Equiv.Perm G) 1 = (σ : Equiv.Perm G) 1 * (τ : Equiv.Perm G) 1 := by
  convert aut_eq_leftMul_of_cayley σ.1 σ.2 ( τ.1 1 ) using 1

/-- The evaluation map eval₁ : Aut → G, sending an automorphism σ to σ(1). -/
noncomputable def evalOneHom (G : Type*) [Group G] :
    (cayleyLabeledDigraph G).autSubgroup →* G where
  toFun σ := (σ : Equiv.Perm G) 1
  map_one' := by simp
  map_mul' σ τ := evalOne_mul_compat σ τ

/-
eval₁ is surjective: for any h ∈ G, left multiplication L_h is an automorphism and L_h(1) = h
-/
theorem evalOneHom_surjective (G : Type*) [Group G] :
    Function.Surjective (evalOneHom G) := by
  intro g
  use ⟨MulAction.toPerm (α := G) (β := G) g, leftMul_isAut G g⟩
  simp [evalOneHom]

/-
eval₁ is injective: if σ(1) = τ(1), then σ = τ by aut_eq_leftMul_of_cayley
-/
theorem evalOneHom_injective (G : Type*) [Group G] :
    Function.Injective (evalOneHom G) := by
  intro σ τ h;
  exact Subtype.ext ( aut_is_leftMul _ σ.2 ▸ aut_is_leftMul _ τ.2 ▸ h ▸ rfl )

/-- **Core theorem**: the automorphism group of the Cayley labeled directed graph is isomorphic to G. -/
noncomputable def cayleyAutMulEquiv (G : Type*) [Group G] :
    (cayleyLabeledDigraph G).autSubgroup ≃* G :=
  MulEquiv.ofBijective (evalOneHom G)
    ⟨evalOneHom_injective G, evalOneHom_surjective G⟩

/-! ============================================================
    Part 7: the general Frucht theorem
    ============================================================ -/

/-- **General Frucht theorem (labeled-directed-graph version)**:
    any finite group is isomorphic to the automorphism group of some labeled directed graph.

    This is a generalization of the classical Frucht theorem. The classical Frucht theorem
    (1939) is for simple undirected graphs and requires the asymmetric-gadget construction.
    The labeled-directed-graph version is given directly via the Cayley labeled directed graph. -/
theorem frucht_labeled_digraph (G : Type*) [Group G] :
    ∃ (D : LabeledDigraph G G),
      Nonempty (D.autSubgroup ≃* G) :=
  ⟨cayleyLabeledDigraph G, ⟨cayleyAutMulEquiv G⟩⟩

/-! ============================================================
    Axiom audit
    ============================================================ -/

#print axioms cayleyAutMulEquiv
#print axioms frucht_labeled_digraph