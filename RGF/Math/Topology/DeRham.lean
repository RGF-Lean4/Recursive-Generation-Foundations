/-
  Discrete differential geometry: the de Rham complex
  Lean support for Paper 13

  Formalizes:
  - discrete 0-forms, 1-forms, and 2-forms
  - the discrete exterior derivatives d₀, d₁
  - a complete proof of d² = 0
  - basic properties of the discrete de Rham complex
-/

import Mathlib

open Finset BigOperators

/-! ## 1. Discrete differential forms -/

/-- A discrete 0-form: a function on vertices. -/
def DiscreteZeroForm (n : ℕ) := Fin n → ℝ

/-- The value function of a discrete 1-form (antisymmetric). -/
structure DiscreteOneForm (n : ℕ) where
  val : Fin n → Fin n → ℝ
  antisymm : ∀ i j, val i j = -val j i

/-- The zero 1-form. -/
def zeroOneForm (n : ℕ) : DiscreteOneForm n where
  val := fun _ _ => 0
  antisymm := by simp

/-- An antisymmetric 1-form vanishes on the diagonal. -/
theorem one_form_diag_zero {n : ℕ} (ω : DiscreteOneForm n) (i : Fin n) :
    ω.val i i = 0 := by
  have h := ω.antisymm i i; linarith

/-! ## 2. Discrete exterior derivative d₀ -/

/-- d₀: the value function from 0-forms to 1-forms
    (d₀ f)(u, v) = f(v) - f(u) -/
def discreteD0 (n : ℕ) (f : DiscreteZeroForm n) : Fin n → Fin n → ℝ :=
  fun i j => f j - f i

/-- d₀ f is antisymmetric. -/
theorem discreteD0_antisymm (n : ℕ) (f : DiscreteZeroForm n)
    (i j : Fin n) :
    discreteD0 n f i j = -(discreteD0 n f j i) := by
  simp [discreteD0]

/-- d₀ produces a valid 1-form. -/
def discreteD0_form (n : ℕ) (f : DiscreteZeroForm n) : DiscreteOneForm n where
  val := discreteD0 n f
  antisymm := discreteD0_antisymm n f

/-- The diagonal value of d₀ is zero. -/
theorem discreteD0_diag (n : ℕ) (f : DiscreteZeroForm n) (i : Fin n) :
    discreteD0 n f i i = 0 := by
  simp [discreteD0]

/-! ## 3. Discrete exterior derivative d₁ -/

/-- d₁: from 1-forms to 2-forms
    (d₁ ω)(u, v, w) = ω(u,v) + ω(v,w) + ω(w,u) -/
def discreteD1 (n : ℕ) (omega : Fin n → Fin n → ℝ) :
    Fin n → Fin n → Fin n → ℝ :=
  fun i j k => omega i j + omega j k + omega k i

/-! ## 4. Core theorem: d² = 0 -/

/-- d₁ ∘ d₀ = 0: the basic property of the de Rham complex. -/
theorem d_squared_zero (n : ℕ) (f : DiscreteZeroForm n)
    (i j k : Fin n) :
    discreteD1 n (discreteD0 n f) i j k = 0 := by
  simp [discreteD1, discreteD0]

/-! ## 5. Further properties of the de Rham complex -/

/-- Antisymmetry of d₁ (swapping the first two arguments). -/
theorem discreteD1_swap12 (n : ℕ)
    (omega : Fin n → Fin n → ℝ)
    (h_anti : ∀ i j, omega i j = -omega j i)
    (i j k : Fin n) :
    discreteD1 n omega j i k = -(discreteD1 n omega i j k) := by
  simp only [discreteD1]
  have h1 := h_anti i j
  have h2 := h_anti j k
  have h3 := h_anti i k
  linarith

/-- The cyclic property of d₁. -/
theorem discreteD1_cyclic (n : ℕ)
    (omega : Fin n → Fin n → ℝ)
    (i j k : Fin n) :
    discreteD1 n omega i j k = discreteD1 n omega j k i := by
  simp [discreteD1]; ring

/-- d₀ preserves addition. -/
theorem discreteD0_add (n : ℕ) (f g : DiscreteZeroForm n)
    (i j : Fin n) :
    discreteD0 n (fun v => f v + g v) i j =
    discreteD0 n f i j + discreteD0 n g i j := by
  simp [discreteD0]; ring

/-- d₀ preserves scalar multiplication. -/
theorem discreteD0_smul (n : ℕ) (c : ℝ) (f : DiscreteZeroForm n)
    (i j : Fin n) :
    discreteD0 n (fun v => c * f v) i j = c * discreteD0 n f i j := by
  simp [discreteD0]; ring

/-- d₀ of a constant function is zero. -/
theorem discreteD0_const (n : ℕ) (c : ℝ) (i j : Fin n) :
    discreteD0 n (fun _ => c) i j = 0 := by
  simp [discreteD0]

/-- Characterization of ker d₀: d₀ f = 0 implies f takes equal values on adjacent vertices. -/
theorem ker_d0_eq_on_edge (n : ℕ) (f : DiscreteZeroForm n)
    (h : ∀ i j : Fin n, discreteD0 n f i j = 0)
    (i j : Fin n) : f i = f j := by
  have := h i j
  simp [discreteD0] at this
  linarith

/-! ## 6. Relation between the discrete Laplacian and d₀ -/

/-- The graph Laplacian defined via d₀: Δf(v) = Σ_{u} (d₀f)(v,u)
    on an unweighted graph, Δf(v) = deg(v)·f(v) - Σ_{u~v} f(u). -/
def graphLaplacianViaD0 (n : ℕ) (adj : Fin n → Fin n → Bool)
    (f : DiscreteZeroForm n) (v : Fin n) : ℝ :=
  ∑ u : Fin n, if adj v u then discreteD0 n f v u else 0

/-- An equivalent expression for the Laplacian. -/
theorem graphLaplacianViaD0_eq (n : ℕ) (adj : Fin n → Fin n → Bool)
    (f : DiscreteZeroForm n) (v : Fin n) :
    graphLaplacianViaD0 n adj f v =
    ∑ u : Fin n, if adj v u then (f u - f v) else 0 := by
  rfl

/-- d₁ of the zero 1-form is zero. -/
theorem discreteD1_zero (n : ℕ) (i j k : Fin n) :
    discreteD1 n (fun _ _ => (0 : ℝ)) i j k = 0 := by
  simp [discreteD1]
