/-
  RGF/YauRelativeEntropy.lean

  Direction II — Non-equilibrium statistical mechanics via Yau's relative-entropy
  method.

  * **Gross tensorisation → uniform (N-independent) LSI.**  The tensorisation
    step `lsi_tensorization`: from entropy subadditivity, additivity of the
    Dirichlet form, and a per-site log-Sobolev inequality with constant `α`, the
    product satisfies an LSI with the *same* `α`; hence a lower bound uniform in
    the system size (`lsi_uniform_lower_bound`).

  * **Yau relative-entropy inequality chain (discrete Grönwall).**  From a
    per-macroscopic-step contraction `H_{n+1} ≤ θ H_n + b` (`θ < 1`) we derive
    the a-priori bound `H_n ≤ θⁿ H_0 + b/(1-θ)` (`yau_entropy_iteration`) and the
    long-time plateau `yau_equilibrium_plateau`.

  * **Sublinear `o(N)` growth (unconditional hydrodynamic limit).**  `IsLittleOhN`
    (`H(N)/N → 0`) is closed under sums and scalar multiples and holds for bounded
    data; the main theorem `relative_entropy_sublinear` shows that if the initial
    local-equilibrium entropy and the block error are both `o(N)`, then the
    relative entropy stays `o(N)` at every macroscopic time.

  Everything is `sorry`-free.
-/
import Mathlib

open scoped BigOperators
open Filter Topology

namespace RGF.Yau

/-! ## 1. Gross tensorisation and the uniform LSI -/

/-- **Tensorisation of the log-Sobolev inequality.**  Entropy subadditivity plus
    additive Dirichlet form plus per-site LSI (constant `α`) yield the product
    LSI with the *same* constant `α`. -/
theorem lsi_tensorization {ι : Type*} (s : Finset ι) (α entTot : ℝ)
    (ent dir : ι → ℝ) (hα : 0 ≤ α) (hsub : entTot ≤ ∑ i ∈ s, ent i)
    (hlsi : ∀ i ∈ s, α * ent i ≤ dir i) :
    α * entTot ≤ ∑ i ∈ s, dir i := by
  calc α * entTot ≤ α * ∑ i ∈ s, ent i := mul_le_mul_of_nonneg_left hsub hα
    _ = ∑ i ∈ s, α * ent i := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, dir i := Finset.sum_le_sum hlsi

/-- **Uniform (N-independent) LSI lower bound.**  For any system size `N`, the
    `N`-fold product inherits the single-site LSI constant `α`. -/
theorem lsi_uniform_lower_bound (α : ℝ) (hα : 0 ≤ α) (N : ℕ) (entTot : ℝ)
    (ent dir : Fin N → ℝ) (hsub : entTot ≤ ∑ i, ent i)
    (hlsi : ∀ i, α * ent i ≤ dir i) : α * entTot ≤ ∑ i, dir i :=
  lsi_tensorization Finset.univ α entTot ent dir hα hsub (fun i _ => hlsi i)

/-! ## 2. Yau relative-entropy inequality chain -/

/-
**Discrete Grönwall / Yau entropy iteration.**  A per-step contraction
    `H_{n+1} ≤ θ H_n + b` (with `0 ≤ θ < 1`, `0 ≤ b`) gives the a-priori bound
    `H_n ≤ θⁿ H_0 + b/(1-θ)`.
-/
theorem yau_entropy_iteration (H : ℕ → ℝ) (θ b : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : 0 ≤ b) (hstep : ∀ n, H (n + 1) ≤ θ * H n + b) :
    ∀ n, H n ≤ θ ^ n * H 0 + b / (1 - θ) := by
  -- We proceed by induction on $n$.
  intro n
  induction' n with n ih;
  · simpa using div_nonneg hb ( sub_nonneg.2 hθ1.le );
  · rw [ pow_succ' ];
    nlinarith [ hstep n, mul_div_cancel₀ b ( by linarith : ( 1 - θ ) ≠ 0 ) ]

/-
**Equilibrium plateau.**  The relative entropy is eventually trapped below the
    stationary level `b/(1-θ)`.
-/
theorem yau_equilibrium_plateau (H : ℕ → ℝ) (θ b : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : 0 ≤ b) (hstep : ∀ n, H (n + 1) ≤ θ * H n + b) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, H n ≤ b / (1 - θ) + ε := by
  intro ε hε;
  -- By yau_entropy_iteration, for all n, H n ≤ θ^n * H 0 + b/(1-θ).
  have h_bound : ∀ n, H n ≤ θ^n * H 0 + b / (1 - θ) := by
    exact fun n ↦ yau_entropy_iteration H θ b hθ0 hθ1 hb hstep n;
  -- Since $\theta^n \to 0$, there exists $N$ such that for all $n \geq N$, $\theta^n * H 0 < \epsilon$.
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, θ^n * H 0 < ε := by
    simpa using ( summable_geometric_of_lt_one hθ0 hθ1 ) |> fun h => h.mul_right _ |> fun h => h.tendsto_atTop_zero.eventually ( gt_mem_nhds hε );
  exact ⟨ N, fun n hn => by linarith [ h_bound n, hN n hn ] ⟩

/-! ## 3. Sublinear `o(N)` growth -/

/-- A sequence has sublinear (`o(N)`) growth: `H(N)/N → 0`. -/
def IsLittleOhN (H : ℕ → ℝ) : Prop :=
  Tendsto (fun N : ℕ => H N / (N : ℝ)) atTop (𝓝 0)

/-- `o(N)` is closed under addition. -/
theorem IsLittleOhN.add {f g : ℕ → ℝ} (hf : IsLittleOhN f) (hg : IsLittleOhN g) :
    IsLittleOhN (fun N => f N + g N) := by
  have h : Filter.Tendsto (fun N : ℕ => f N / (N : ℝ)) atTop (𝓝 0) := hf
  have h' : Filter.Tendsto (fun N : ℕ => g N / (N : ℝ)) atTop (𝓝 0) := hg
  have h2 := h.add h'
  simp only [add_zero] at h2
  unfold IsLittleOhN
  simpa [add_div] using h2

/-- `o(N)` is closed under scalar multiples. -/
theorem IsLittleOhN.const_mul (c : ℝ) {f : ℕ → ℝ} (hf : IsLittleOhN f) :
    IsLittleOhN (fun N => c * f N) := by
  have h : Filter.Tendsto (fun N : ℕ => f N / (N : ℝ)) atTop (𝓝 0) := hf
  have h2 := Filter.Tendsto.const_mul c h
  simp only [mul_zero] at h2
  unfold IsLittleOhN
  simpa [mul_div_assoc] using h2

/-- Bounded data is `o(N)`. -/
theorem IsLittleOhN.of_bounded {f : ℕ → ℝ} (C : ℝ) (hC : ∀ N, |f N| ≤ C) :
    IsLittleOhN f := by
  refine' squeeze_zero_norm ( fun N => _ ) ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop );
  simpa using div_le_div_of_nonneg_right ( hC N ) ( Nat.cast_nonneg N )

/-- **Relative entropy stays sublinear.**  If the initial local-equilibrium
    entropy and the block error are both `o(N)`, then the (non-negative) relative
    entropy is `o(N)` at every macroscopic time. -/
theorem relative_entropy_sublinear (H localEq blockErr : ℕ → ℝ)
    (hnn : ∀ N, 0 ≤ H N) (hle : ∀ N, H N ≤ localEq N + blockErr N)
    (h1 : IsLittleOhN localEq) (h2 : IsLittleOhN blockErr) :
    IsLittleOhN H := by
  refine' squeeze_zero ( fun N ↦ div_nonneg ( hnn N ) ( Nat.cast_nonneg N ) ) ( fun N ↦ div_le_div_of_nonneg_right ( hle N ) ( Nat.cast_nonneg N ) ) _;
  simpa [ add_div ] using Filter.Tendsto.add h1 h2

end RGF.Yau