/-
  Graph coloring and the chromatic number
  Graph Coloring and Chromatic Number

  Reference paper: 39. Quintic structures in graph theory and combinatorial design
-/

import Mathlib
import RGF.Math.Graph.GraphAutomorphism

open Finset BigOperators SimpleGraph

/-! ## 1. Definition of graph coloring -/

/-- A k-coloring: a function f : V → Fin k assigning different colors to adjacent vertices. -/
def SimpleGraph.IsProperColoring {V : Type*} (G : SimpleGraph V)
    (k : ℕ) (f : V → Fin k) : Prop :=
  ∀ u v, G.Adj u v → f u ≠ f v

/-- The graph G is k-colorable. -/
def SimpleGraph.IsColorable {V : Type*} (G : SimpleGraph V)
    (k : ℕ) : Prop :=
  ∃ f : V → Fin k, G.IsProperColoring k f

/-! ## 2. The chromatic number of complete graphs -/

/-- K_n cannot be colored with fewer than n colors. -/
theorem complete_graph_chromatic_lower (n : ℕ) (k : ℕ) (hk : k < n) :
    ¬ (⊤ : SimpleGraph (Fin n)).IsColorable k := by
  intro ⟨f, hf⟩
  have hinj : Function.Injective f := by
    intro u v huv
    by_contra hne
    have : (⊤ : SimpleGraph (Fin n)).Adj u v := by simpa using hne
    exact absurd huv (hf u v this)
  have hcard := Fintype.card_le_of_injective f hinj
  simp at hcard
  omega

/-- K_n can be colored with n colors. -/
theorem complete_graph_chromatic_upper (n : ℕ) :
    (⊤ : SimpleGraph (Fin n)).IsColorable n :=
  ⟨id, fun u v h => by simpa using h⟩

/-- K₅ cannot be colored with 4 colors. -/
theorem k5_not_4_colorable :
    ¬ (⊤ : SimpleGraph (Fin 5)).IsColorable 4 :=
  complete_graph_chromatic_lower 5 4 (by omega)

/-- K₅ can be colored with 5 colors. -/
theorem k5_5_colorable :
    (⊤ : SimpleGraph (Fin 5)).IsColorable 5 :=
  complete_graph_chromatic_upper 5

/-! ## 3. Coloring of C₅ -/

/-- C₅ can be colored with 3 colors. -/
theorem c5_3_colorable :
    c5Graph.IsColorable 3 := by
  refine ⟨![0, 1, 2, 0, 1], ?_⟩
  intro u v huv
  fin_cases u <;> fin_cases v <;> simp_all [c5Graph, c5AdjMatrix]

/-- C₅ cannot be colored with 2 colors. -/
theorem c5_not_2_colorable :
    ¬ c5Graph.IsColorable 2 := by
  intro ⟨f, hf⟩
  have h01 := hf 0 1 (by decide)
  have h12 := hf 1 2 (by decide)
  have h23 := hf 2 3 (by decide)
  have h34 := hf 3 4 (by decide)
  have h40 := hf 4 0 (by decide)
  -- C₅ is an odd cycle, so 2-coloring is impossible
  -- In Fin 2, a ≠ b means they are the two distinct elements
  -- So consecutive ≠ forces alternation: f0, f1, f0, f1, f0
  -- Then f 4 = f 0, contradicting h40
  have two_val : ∀ x : Fin 2, x.val = 0 ∨ x.val = 1 := by
    intro x; omega
  have ne_fin2 : ∀ x y : Fin 2, x ≠ y → x.val ≠ y.val := by
    intro x y h hv; exact h (Fin.ext hv)
  have h02 : f 0 = f 2 := by
    have hv01 := ne_fin2 _ _ h01
    have hv12 := ne_fin2 _ _ h12
    rcases two_val (f 0), two_val (f 1), two_val (f 2) with
      ⟨h0 | h0, h1 | h1, h2 | h2⟩ <;> (try omega)
  have h24 : f 2 = f 4 := by
    have hv23 := ne_fin2 _ _ h23
    have hv34 := ne_fin2 _ _ h34
    rcases two_val (f 2), two_val (f 3), two_val (f 4) with
      ⟨h2 | h2, h3 | h3, h4 | h4⟩ <;> (try omega)
  exact h40 (h24.symm.trans h02.symm)

/-! ## 4. Greedy upper bound -/

/-
Greedy coloring: a graph of degree ≤ Δ is (Δ+1)-colorable
-/
theorem greedy_coloring_bound (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (Δ : ℕ)
    (hdeg : ∀ v : Fin n, (G.neighborFinset v).card ≤ Δ) :
    G.IsColorable (Δ + 1) := by
  obtain ⟨c, hc⟩ : ∃ c : Fin n → Fin (Δ + 1), ∀ u v, G.Adj u v → c u ≠ c v := by
    have h_colorable : ∀ (s : Finset (Fin n)), ∃ c : Fin n → Fin (Δ + 1), ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
      intro s
      induction' s using Finset.induction with u s ih;
      · exact ⟨ fun _ => 0, by simp +decide ⟩;
      · obtain ⟨ c, hc ⟩ := ‹_›;
        -- Choose a color for $u$ that is different from the colors of its neighbors in $s$.
        obtain ⟨color_u, hcolor_u⟩ : ∃ color_u : Fin (Δ + 1), ∀ v ∈ s, G.Adj u v → color_u ≠ c v := by
          have h_color_u : Finset.card (Finset.image c (Finset.filter (fun v => G.Adj u v) s)) ≤ Δ := by
            exact le_trans ( Finset.card_image_le ) ( le_trans ( Finset.card_le_card ( show Finset.filter ( fun v => G.Adj u v ) s ⊆ G.neighborFinset u from fun x hx => by aesop ) ) ( hdeg u ) );
          contrapose! h_color_u;
          rw [ show Finset.image c ( Finset.filter ( fun v => G.Adj u v ) s ) = Finset.univ from Finset.eq_univ_of_forall fun x => by obtain ⟨ v, hv₁, hv₂, rfl ⟩ := h_color_u x; exact Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hv₁, hv₂ ⟩ ) ] ; simp +decide [ Finset.card_univ ];
        use fun v => if v = u then color_u else c v; simp_all +decide [ SimpleGraph.adj_comm ] ;
        grind;
    exact Exists.elim ( h_colorable Finset.univ ) fun c hc => ⟨ c, fun u v huv => hc u ( Finset.mem_univ u ) v ( Finset.mem_univ v ) huv ⟩;
  exact ⟨ c, hc ⟩

/-! ## 5. Connection with quintic locking -/

/-- The chromatic number and quintic locking. -/
theorem chromatic_five_locking :
    (¬ (⊤ : SimpleGraph (Fin 5)).IsColorable 4 ∧
     (⊤ : SimpleGraph (Fin 5)).IsColorable 5) ∧
    (¬ c5Graph.IsColorable 2 ∧ c5Graph.IsColorable 3) :=
  ⟨⟨k5_not_4_colorable, k5_5_colorable⟩,
   ⟨c5_not_2_colorable, c5_3_colorable⟩⟩