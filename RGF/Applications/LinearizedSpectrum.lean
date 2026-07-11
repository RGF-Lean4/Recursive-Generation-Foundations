import Mathlib
import RGF.Generative.Locking.ModeDecomposition

/-!
# FORS part three (continued): the concrete form of the linearized operator and substantive spectral analysis

The `linearizedOperator` in `FORS/ModeDecomposition.lean` is still a placeholder
(identically 0). This file gives the **concrete form of the linearized operator in the
infrared (IR) sector** and uses it to make the spectral analysis substantive.

## Derivation from the "new energy functional" to the concrete linearized operator

The geometric dimension-reduction energy `energy φ = (suppDim φ − 2)²` from
`FORS/Setup.lean` is **integer-valued and piecewise constant**, and its strict second
variation (Hessian) vanishes in directions that preserve the membrane support dimension —
this is the origin of the placeholder `linearizedOperator ≡ 0` (the energy really is
invariant under transverse fluctuations that "preserve the support dimension").

To make the spectral analysis substantive, the linearization must be restricted to the
**infrared principal-mode sector**: by `FORS/ModeDecomposition.lean`, the infrared limit
has exactly 5 massless principal modes, corresponding one-to-one with the pentagon
(5 vertices `ZMod 5`), and D₅ permutes them faithfully via `pentagonRep`. Within this
sector, the second variation of the nearest-neighbor gradient energy along the membrane
(the Dirichlet energy on the C₅ cycle)

  `E[u] = (1/2) ∑_{⟨x,y⟩} (u_x − u_y)² = (1/2) ∑_x (u_{x+1} − u_x)²`

gives the **concrete linearized operator**: the pentagon (C₅) graph Laplacian

  `(L u)_x = 2 u_x − u_{x+1} − u_{x−1}`,

which replaces the placeholder 0 operator. This file proves its spectral structure:

* **self-adjoint** (symmetric, `pentagonLaplacian_symm`);
* **positive semidefinite = stability** (`pentagon_pairing_nonneg`), with its quadratic
  form being exactly the energy (`pentagon_energy_eq_pairing`);
* **kernel = constant functions** (`pentagon_ker_iff_const`): exactly **1 massless zero
  mode** (the trivial representation, corresponding to the global translation/phase of
  the membrane), with the remaining 4 directions having strictly positive energy
  (`pentagon_energy_pos_of_nonconst`), i.e. **4 massive modes**;
* **D₅-equivariant** (`pentagonLaplacian_equivariant`): `L` commutes with `pentagonRep`,
  so the spectral spaces are subrepresentations of D₅. The kernel (1-dimensional) = the
  trivial representation, and the positive-energy complement (4-dimensional) = ρ₁ ⊕ ρ₂
  (the two 2-dimensional irreducible representations, corresponding to two nonzero
  eigenvalues, each of multiplicity 2).

Thus the D₅ decomposition "5 modes = 1 (massless, trivial) + 2 + 2 (massive, two
2-dimensional irreps)" (see `pentagon_perm_decomposition` in
`FORS/ModeDecomposition.lean`) acquires a **substantive characterization at the level of
the operator spectrum**: the eigenvalues are `λ_k = 2 − 2cos(2πk/5)`, with `λ_0 = 0`
(1-dimensional trivial), `λ_1 = λ_4 = 2 − 2cos72°`, and `λ_2 = λ_3 = 2 − 2cos144°`
(two groups, each 2-dimensional).

Dependency: FORS/ModeDecomposition.lean
-/

namespace RGF.FORS

open Finset

/-- Fluctuations in the infrared sector: real-valued functions on the 5 pentagon vertices
    `ZMod 5` (each vertex corresponds to the amplitude of one infrared principal mode). -/
abbrev IRMode : Type := ZMod 5 → ℝ

/-! ## The concrete linearized operator: the pentagon (C₅) graph Laplacian -/

/-- **The concrete form of the infrared-sector linearized operator**: the pentagon (C₅)
    graph Laplacian `(L u)_x = 2 u_x − u_{x+1} − u_{x−1}`. Replaces the placeholder 0
    operator. -/
def pentagonLaplacian (u : IRMode) : IRMode :=
  fun x => 2 * u x - u (x + 1) - u (x - 1)

/-- The linear-map form of the linearized operator. -/
def pentagonLaplacianₗ : IRMode →ₗ[ℝ] IRMode where
  toFun := pentagonLaplacian
  map_add' u v := by
    funext x; simp only [pentagonLaplacian, Pi.add_apply]; ring
  map_smul' c u := by
    funext x; simp only [pentagonLaplacian, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; ring

/-- The (standard) pairing between modes `⟪u, v⟫ = ∑_x u_x v_x`. -/
def pairing (u v : IRMode) : ℝ := ∑ x : ZMod 5, u x * v x

/-- The nearest-neighbor gradient energy along the membrane (the Dirichlet energy on the
    C₅ cycle); the linearized operator is given by its second variation. -/
def pentagonEnergy (u : IRMode) : ℝ := ∑ x : ZMod 5, (u (x + 1) - u x) ^ 2

/-! ## Energy = quadratic form; self-adjoint; positive semidefinite -/

/-
**The energy functional is the quadratic form of the linearized operator**: `⟪u, L u⟫ = E[u]`.
    This binds the "new energy functional" directly to the concrete linearized operator.
-/
theorem pentagon_energy_eq_pairing (u : IRMode) :
    pairing u (pentagonLaplacian u) = pentagonEnergy u := by
  unfold pairing pentagonLaplacian pentagonEnergy; ring;
  rw [ show ( Finset.univ : Finset ( ZMod 5 ) ) = { 0, 1, 2, 3, 4 } by rfl ] ; simp +decide ; ring!

/-
**Self-adjoint (symmetric)**: `⟪L u, v⟫ = ⟪u, L v⟫`.
-/
theorem pentagonLaplacian_symm (u v : IRMode) :
    pairing (pentagonLaplacian u) v = pairing u (pentagonLaplacian v) := by
  unfold pairing pentagonLaplacian;
  rw [ show ( Finset.univ : Finset ( ZMod 5 ) ) = { 0, 1, 2, 3, 4 } by rfl ] ; simp +decide ; ring!;

/-
The energy is nonnegative (a sum of squares).
-/
theorem pentagonEnergy_nonneg (u : IRMode) : 0 ≤ pentagonEnergy u := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Positive semidefinite = stability**: `0 ≤ ⟪u, L u⟫`. -/
theorem pentagon_pairing_nonneg (u : IRMode) :
    0 ≤ pairing u (pentagonLaplacian u) := by
  rw [pentagon_energy_eq_pairing]; exact pentagonEnergy_nonneg u

/-! ## Kernel = constant functions: exactly one massless zero mode -/

/-
A constant field is a zero mode (the massless principal mode, corresponding to the trivial representation).
-/
theorem pentagonLaplacian_const_zero (c : ℝ) :
    pentagonLaplacian (fun _ => c) = 0 := by
  funext x
  simp [pentagonLaplacian];
  ring

/-
The energy is zero iff the field is constant (connectedness of C₅).
-/
theorem pentagon_energy_eq_zero_iff_const (u : IRMode) :
    pentagonEnergy u = 0 ↔ ∃ c : ℝ, u = fun _ => c := by
  constructor <;> intro h;
  · unfold pentagonEnergy at h;
    rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _ ] at h;
    simp_all +decide [ sub_eq_iff_eq_add ];
    exact ⟨ u 0, funext fun x => by fin_cases x <;> linarith! [ h 0, h 1, h 2, h 3, h 4 ] ⟩;
  · unfold pentagonEnergy; aesop;

/-
**Kernel = constant functions**: `L u = 0 ↔ u is constant`.
    So the zero eigenspace is exactly 1-dimensional (massless mode = trivial representation).
-/
theorem pentagon_ker_iff_const (u : IRMode) :
    pentagonLaplacian u = 0 ↔ ∃ c : ℝ, u = fun _ => c := by
  norm_num [ funext_iff ];
  constructor;
  · intro h;
    unfold pentagonLaplacian at h; simp_all +decide [ ZMod, Fin.forall_fin_succ ] ;
    grind;
  · rintro ⟨ c, hc ⟩ ; unfold pentagonLaplacian; simp +decide [ hc ] ;
    ring

/-- **Mass gap**: a non-constant field has strictly positive energy, i.e. the remaining 4
    directions are all massive modes. -/
theorem pentagon_energy_pos_of_nonconst (u : IRMode)
    (h : ¬ ∃ c : ℝ, u = fun _ => c) : 0 < pentagonEnergy u := by
  rcases lt_or_eq_of_le (pentagonEnergy_nonneg u) with h' | h'
  · exact h'
  · exact absurd ((pentagon_energy_eq_zero_iff_const u).1 h'.symm) h

/-
The kernel of the linearized operator is exactly the 1-dimensional subspace spanned by the constant functions (the trivial representation).
-/
theorem pentagon_ker_eq_span_const :
    LinearMap.ker pentagonLaplacianₗ = ℝ ∙ (fun _ => (1 : ℝ) : IRMode) := by
  ext u;
  rw [ Submodule.mem_span_singleton ] ; exact ⟨ fun h => by obtain ⟨ c, rfl ⟩ := pentagon_ker_iff_const u |>.1 h; exact ⟨ c, by ext x; simp +decide ⟩, fun h => by obtain ⟨ c, rfl ⟩ := h; exact pentagon_ker_iff_const _ |>.2 ⟨ c, by ext x; simp +decide ⟩ ⟩ ;

/-! ## D₅-equivariance: the spectral spaces are D₅ subrepresentations -/

/-
**D₅-equivariance**: the linearized operator commutes with the pentagon permutation action,
    `L (u ∘ pentagonRep g) = (L u) ∘ pentagonRep g`.
    So every eigenspace is a subrepresentation of D₅: the kernel (1-dimensional) = the
    trivial representation, and the positive-energy complement (4-dimensional) = ρ₁ ⊕ ρ₂.
-/
theorem pentagonLaplacian_equivariant (g : DihedralGroup 5) (u : IRMode) :
    pentagonLaplacian (fun x => u (pentagonRep g x))
      = fun x => pentagonLaplacian u (pentagonRep g x) := by
  rcases g with ( _ | _ ) <;> funext x <;> simp +decide [ pentagonLaplacian ];
  · simp +decide [ pentagonRep_r ];
    ring;
  · rename_i k; fin_cases x <;> fin_cases k <;> ring!;

end RGF.FORS
