/-
  Toric Code — general lattice homology (any size `L`).

  This module upgrades the fixed-size (`L = 3`) numeric facts of
  `RGF.Physics.Dynamics.ToricCode` — stabilizer rank, number of logical qubits,
  and the four-fold ground-state degeneracy — from *worked examples verified by
  machine evaluation* (`native_decide`) to *theorems proved uniformly for every
  torus size* `L`.

  Following the linear-algebra shortcut (rather than rebuilding cellular
  homology): the degeneracy question is reduced to the rank of the GF(2)
  incidence (coboundary) map of the torus grid.  For a connected graph the GF(2)
  rank of the vertex–edge incidence map equals `#vertices − #components`, and the
  torus grid `T²` is connected (one component), so each of the two coboundary
  maps (vertices/plaquettes) has rank `L² − 1`.  Hence

    k = n − r = 2L² − 2(L² − 1) = 2      (number of logical qubits)
    ground degeneracy = 2^k = 4          (for every `L ≥ 1`, in particular `L ≥ 2`)

  and `k = 2 = dim H₁(T² ; ℤ₂)`.

  Concretely we work with the two GF(2) *coboundary* linear maps
    δ_V : (Site → 𝔽₂) → (Edge → 𝔽₂),  (δ_V f)(e) = f(∂₀e) + f(∂₁e)
  (vertices) and its plaquette analogue δ_P.  Their **kernels are exactly the
  constant functions** (a `1`-dimensional space, because the torus grid is
  connected: shift-invariance in both directions forces a function on `ZMod L ×
  ZMod L` to be constant).  By rank–nullity the ranges therefore have dimension
  `L² − 1`, and the counting above follows.
-/

import Mathlib

open scoped BigOperators

namespace RGF.ToricCodeGeneral

variable (L : ℕ)

/-- A site (vertex / plaquette label) of the `L × L` torus. -/
abbrev Site := ZMod L × ZMod L

/-- An edge of the torus: a direction (`0` = horizontal, `1` = vertical) with a
    base site.  Qubits live on edges; there are `2L²` of them. -/
abbrev Edge := Fin 2 × ZMod L × ZMod L

section
variable [NeZero L]

/-! ### The GF(2) coboundary maps -/

/-- The vertex coboundary map `δ_V` over `GF(2) = ZMod 2`.  A horizontal edge at
    `(x,y)` joins the vertices `(x,y)` and `(x+1,y)`; a vertical edge at `(x,y)`
    joins `(x,y)` and `(x,y+1)`.  `(δ_V f)(e)` is the sum of `f` over the two
    endpoints of `e`. -/
def deltaV : (Site L → ZMod 2) →ₗ[ZMod 2] (Edge L → ZMod 2) where
  toFun f := fun e =>
    if e.1 = 0 then f (e.2.1, e.2.2) + f (e.2.1 + 1, e.2.2)
    else f (e.2.1, e.2.2) + f (e.2.1, e.2.2 + 1)
  map_add' f g := by funext e; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c f := by
    funext e; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; split_ifs <;> ring

/-- The plaquette coboundary map `δ_P` over `GF(2)`.  A horizontal edge at
    `(x,y)` bounds the plaquettes `(x,y)` and `(x,y-1)`; a vertical edge at
    `(x,y)` bounds `(x,y)` and `(x-1,y)`.  `(δ_P g)(e)` is the sum of `g` over the
    two plaquettes bounded by `e`. -/
def deltaP : (Site L → ZMod 2) →ₗ[ZMod 2] (Edge L → ZMod 2) where
  toFun g := fun e =>
    if e.1 = 0 then g (e.2.1, e.2.2) + g (e.2.1, e.2.2 - 1)
    else g (e.2.1, e.2.2) + g (e.2.1 - 1, e.2.2)
  map_add' f g := by funext e; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c f := by
    funext e; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; split_ifs <;> ring

/-! ### The kernels are the constant functions (connectivity of the torus) -/

/-- **Connectivity, vertex form.**  Any function in the kernel of `δ_V` is
    constant: shift-invariance in both lattice directions forces a function on
    `ZMod L × ZMod L` to be constant (the torus grid is connected). -/
theorem constV {f : Site L → ZMod 2} (hf : f ∈ LinearMap.ker (deltaV L)) :
    ∀ p : Site L, f p = f 0 := by
  have h0 : deltaV L f = 0 := hf
  have key : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  have const1 : ∀ {g : ZMod L → ZMod 2}, (∀ a, g (a + 1) = g a) → ∀ a, g a = g 0 := by
    intro g hg a
    have hn : ∀ n : ℕ, g (n : ZMod L) = g 0 := by
      intro n; induction n with
      | zero => simp
      | succ k ih => rw [Nat.cast_succ]; exact (hg _).trans ih
    have hval : ((a.val : ℕ) : ZMod L) = a := ZMod.natCast_zmod_val a
    rw [← hval]; exact hn a.val
  have hx : ∀ (x y : ZMod L), f (x + 1, y) = f (x, y) := by
    intro x y
    have hc := congrFun h0 (0, x, y)
    simp only [deltaV, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, if_pos] at hc
    exact key _ _ hc
  have hy : ∀ (x y : ZMod L), f (x, y + 1) = f (x, y) := by
    intro x y
    have hc := congrFun h0 (1, x, y)
    simp only [deltaV, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hc
    exact key _ _ hc
  intro p
  obtain ⟨x, y⟩ := p
  have cx : f (x, y) = f (0, y) := const1 (g := fun x => f (x, y)) (fun a => hx a y) x
  have cy : f (0, y) = f (0, 0) := const1 (g := fun y => f (0, y)) (fun a => hy 0 a) y
  rw [cx, cy]; rfl

/-- **Connectivity, plaquette form.**  Any function in the kernel of `δ_P` is
    constant (the dual grid of the torus is connected too). -/
theorem constP {f : Site L → ZMod 2} (hf : f ∈ LinearMap.ker (deltaP L)) :
    ∀ p : Site L, f p = f 0 := by
  have h0 : deltaP L f = 0 := hf
  have key : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  have const1 : ∀ {g : ZMod L → ZMod 2}, (∀ a, g (a + 1) = g a) → ∀ a, g a = g 0 := by
    intro g hg a
    have hn : ∀ n : ℕ, g (n : ZMod L) = g 0 := by
      intro n; induction n with
      | zero => simp
      | succ k ih => rw [Nat.cast_succ]; exact (hg _).trans ih
    have hval : ((a.val : ℕ) : ZMod L) = a := ZMod.natCast_zmod_val a
    rw [← hval]; exact hn a.val
  -- From the `d = 0` edges: f(x,y) + f(x,y-1) = 0 ⇒ f(x,y-1) = f(x,y);
  -- evaluate at `(0, x, y+1)` so that `(y+1)-1 = y` and we get the `+1` relation.
  have hy : ∀ (x y : ZMod L), f (x, y + 1) = f (x, y) := by
    intro x y
    have hc := congrFun h0 (0, x, y + 1)
    simp only [deltaP, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, if_true,
      add_sub_cancel_right] at hc
    exact (key _ _ hc).symm
  have hx : ∀ (x y : ZMod L), f (x + 1, y) = f (x, y) := by
    intro x y
    have hc := congrFun h0 (1, x + 1, y)
    simp only [deltaP, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
      add_sub_cancel_right] at hc
    exact (key _ _ hc).symm
  intro p
  obtain ⟨x, y⟩ := p
  have cx : f (x, y) = f (0, y) := const1 (g := fun x => f (x, y)) (fun a => hx a y) x
  have cy : f (0, y) = f (0, 0) := const1 (g := fun y => f (0, y)) (fun a => hy 0 a) y
  rw [cx, cy]; rfl

/-! ### The kernels are one-dimensional -/

/-- `ker δ_V ≃ 𝔽₂` : the kernel is the line of constant functions. -/
def kerEquivV : (LinearMap.ker (deltaV L)) ≃ₗ[ZMod 2] ZMod 2 where
  toFun x := x.1 0
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun c := ⟨fun _ => c, by
    simp only [LinearMap.mem_ker]
    funext e
    simp only [deltaV, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    split_ifs <;> exact CharTwo.add_self_eq_zero c⟩
  left_inv x := by
    apply Subtype.ext; funext p; exact (constV L x.2 p).symm
  right_inv c := rfl

/-- `ker δ_P ≃ 𝔽₂` : the kernel is the line of constant functions. -/
def kerEquivP : (LinearMap.ker (deltaP L)) ≃ₗ[ZMod 2] ZMod 2 where
  toFun x := x.1 0
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun c := ⟨fun _ => c, by
    simp only [LinearMap.mem_ker]
    funext e
    simp only [deltaP, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    split_ifs <;> exact CharTwo.add_self_eq_zero c⟩
  left_inv x := by
    apply Subtype.ext; funext p; exact (constP L x.2 p).symm
  right_inv c := rfl

theorem finrank_ker_deltaV : Module.finrank (ZMod 2) (LinearMap.ker (deltaV L)) = 1 := by
  rw [LinearEquiv.finrank_eq (kerEquivV L)]; exact Module.finrank_self _

theorem finrank_ker_deltaP : Module.finrank (ZMod 2) (LinearMap.ker (deltaP L)) = 1 := by
  rw [LinearEquiv.finrank_eq (kerEquivP L)]; exact Module.finrank_self _

/-! ### The ranks are `L² − 1` -/

theorem finrank_range_deltaV :
    Module.finrank (ZMod 2) (LinearMap.range (deltaV L)) + 1 = L * L := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (deltaV L)
  have hk := finrank_ker_deltaV L
  have hdom : Module.finrank (ZMod 2) (Site L → ZMod 2) = L * L := by
    rw [Module.finrank_fintype_fun_eq_card]; simp [Fintype.card_prod, ZMod.card]
  rw [hk, hdom] at hrk; omega

theorem finrank_range_deltaP :
    Module.finrank (ZMod 2) (LinearMap.range (deltaP L)) + 1 = L * L := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (deltaP L)
  have hk := finrank_ker_deltaP L
  have hdom : Module.finrank (ZMod 2) (Site L → ZMod 2) = L * L := by
    rw [Module.finrank_fintype_fun_eq_card]; simp [Fintype.card_prod, ZMod.card]
  rw [hk, hdom] at hrk; omega

/-! ### The toric-code counting -/

/-- Number of physical qubits `n = |Edge| = 2L²`. -/
def numPhysical : ℕ := Fintype.card (Edge L)

/-- Total dimension of the stabilizer subspace of the symplectic `GF(2)` space:
    the `X`-type (vertex) generators and `Z`-type (plaquette) generators live in
    independent blocks, so the dimension is the sum of the two coboundary ranks,
    `r = rank δ_V + rank δ_P`. -/
noncomputable def stabDim : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (deltaV L)) +
  Module.finrank (ZMod 2) (LinearMap.range (deltaP L))

/-- Number of logical qubits `k = n − r`.  Equivalently `dim H₁(T² ; ℤ₂)`. -/
noncomputable def numLogical : ℕ := numPhysical L - stabDim L

/-- Ground-space degeneracy `2^k`. -/
noncomputable def groundDegeneracy : ℕ := 2 ^ numLogical L

theorem numPhysical_eq : numPhysical L = 2 * (L * L) := by
  simp [numPhysical, Fintype.card_prod, ZMod.card]

/-- **Number of logical qubits is `2` for every torus size** (the request states
    `L ≥ 2`; the hypothesis `2 ≤ L` is kept per the request although the argument
    in fact holds for every `L ≥ 1`).  This is `dim H₁(T² ; ℤ₂) = 2`. -/
theorem numLogical_eq (hL : 2 ≤ L) : numLogical L = 2 := by
  have _pos : 0 < L := by omega
  have hp : numPhysical L = 2 * (L * L) := numPhysical_eq L
  have hv := finrank_range_deltaV L
  have hpl := finrank_range_deltaP L
  simp only [numLogical, stabDim]
  omega

/-- **Topological ground-state degeneracy is four for every torus size**
    `L ≥ 2`: `2^(n − r) = 2² = 4`.  This upgrades the fixed `L = 3`
    `native_decide` computation of `ToricCode.ground_degeneracy_eq_four` to a
    theorem uniform in `L`. -/
theorem groundDegeneracy_eq_four (hL : 2 ≤ L) : groundDegeneracy L = 4 := by
  have h : numLogical L = 2 := numLogical_eq L hL
  simp [groundDegeneracy, h]

end

end RGF.ToricCodeGeneral
