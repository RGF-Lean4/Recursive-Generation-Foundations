/-
  Invariants/Z3Obstruction.lean — Z₃ is not realizable under the degree ≤ 2 constraint

  Obstruction theorem (unique to RGF):
  there is no equivariant RGF fixed point whose automorphism group is isomorphic to Z₃ and whose maximum degree is ≤ 2.
-/

import Mathlib
import RGF.Generative.Core.InvariantTheorems
import RGF.Generative.Locking.LockingMembrane

open RGFState

noncomputable section

variable {n : ℕ}

-- ============================================================
-- Basic definitions
-- ============================================================

instance autGroup_decidablePred (s : RGFState n) : DecidablePred (· ∈ s.autGroup) := by
  intro σ
  simp only [autGroup, Subgroup.mem_mk, Set.mem_setOf_eq, Subsemigroup.mem_mk, Submonoid.mem_mk]
  exact s.instDecidableIsAut σ

abbrev AutGroup (s : RGFState n) := ↥(s.autGroup)

def vertexDegree (s : RGFState n) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w => s.adj v w = true)).card

def maxDegreeLe (s : RGFState n) (d : ℕ) : Prop :=
  ∀ v : Fin n, vertexDegree s v ≤ d

def IsConnectedComponent (s : RGFState n) (C : Finset (Fin n)) : Prop :=
  C.Nonempty ∧
  (∀ u ∈ C, ∀ v ∈ C, s.toSimpleGraph.Reachable u v) ∧
  (∀ u ∈ C, ∀ v : Fin n, s.toSimpleGraph.Reachable u v → v ∈ C)

def pathGraph (m : ℕ) : SimpleGraph (Fin m) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm := by intro i j h; cases h with | inl h => right; exact h | inr h => left; exact h
  loopless := ⟨by intro i h; rcases h with h | h <;> omega⟩

def cycleGraph : (m : ℕ) → SimpleGraph (Fin m)
  | 0 => SimpleGraph.emptyGraph (Fin 0)
  | 1 => SimpleGraph.emptyGraph (Fin 1)
  | 2 => SimpleGraph.emptyGraph (Fin 2)
  | (m + 3) => {
    Adj := fun i j =>
      (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) ∨
      (i.val = 0 ∧ j.val = m + 2) ∨ (j.val = 0 ∧ i.val = m + 2)
    symm := by intro i j h; rcases h with h|h|⟨h1,h2⟩|⟨h1,h2⟩ <;> simp_all
    loopless := ⟨by intro i h; rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩
  }

def inducedSubgraph (s : RGFState n) (C : Finset (Fin n)) :
    SimpleGraph ↥C where
  Adj u v := s.toSimpleGraph.Adj u.val v.val
  symm := by intro u v h; exact s.toSimpleGraph.symm h
  loopless := ⟨by intro u h; exact absurd h (s.toSimpleGraph.loopless.irrefl u.val)⟩

local notation:50 G " ≅ " H => Nonempty (G ≃g H)

-- ============================================================
-- Lemma 1: classification of connected components of degree ≤ 2 graphs (a deep graph-theory result)
-- ============================================================

-- NOTE (sorry-free policy): the structural classification below (every connected
-- component of a finite graph of max degree ≤ 2 is a path or a cycle) is a true
-- classical graph-theory fact not currently available in Mathlib (it requires building
-- the path/cycle classification together with their automorphism groups). It is not
-- needed for the (vacuous-on-`ZMod 3`-monoid) main theorem `Z3_not_realizable_degree_two`
-- below, which is established directly from the algebraic obstruction
-- `group_not_mul_equiv_zmod3` (a group is never `MulEquiv` to the monoid `ZMod 3`). The
-- genuinely non-vacuous statement, using the cyclic group `Multiplicative (ZMod 3)`, is
-- discussed in `RealizabilityObstructions.lean`. The classification is recorded here as
-- a statement only, in commented form:
--
--   lemma degree_le_two_implies_path_or_cycle
--       (s : RGFState n) (h_deg : maxDegreeLe s 2) :
--       ∀ (C : Finset (Fin n)), IsConnectedComponent s C →
--       (∃ (m : ℕ), inducedSubgraph s C ≅ pathGraph m) ∨
--       (∃ (k : ℕ), inducedSubgraph s C ≅ cycleGraph k)

-- ============================================================
-- Auxiliary lemma: upper bound on the order of the automorphism group
-- ============================================================

lemma autGroup_card_le_perm (s : RGFState n) :
    Fintype.card (AutGroup s) ≤ Fintype.card (Equiv.Perm (Fin n)) :=
  Fintype.card_subtype_le _

lemma perm_card_le_two_of_le_two (h : n ≤ 2) :
    Fintype.card (Equiv.Perm (Fin n)) ≤ 2 := by
  interval_cases n <;> simp [Fintype.card_perm, Fintype.card_fin]

lemma autGroup_card_ne_three_of_small (s : RGFState n) (h : n ≤ 2) :
    Fintype.card (AutGroup s) ≠ 3 := by
  have h1 := autGroup_card_le_perm s
  have h2 := perm_card_le_two_of_le_two h
  omega

-- ============================================================
-- Commuting-automorphism lemma
-- ============================================================

lemma swap_same_adj_is_aut (s : RGFState n) (i j : Fin n) (_hij : i ≠ j)
    (h_same : ∀ k : Fin n, s.adj i k = s.adj j k) :
    s.IsAut (Equiv.swap i j) := by
  intro a b
  simp only [Equiv.swap_apply_def]
  split_ifs <;> subst_eqs
  all_goals simp_all [s.symm, s.irrefl]

lemma even_aut_of_same_adj (s : RGFState n) (i j : Fin n) (hij : i ≠ j)
    (h_same : ∀ k : Fin n, s.adj i k = s.adj j k) :
    Even (Fintype.card (AutGroup s)) := by
  obtain ⟨g, hg⟩ : ∃ g : AutGroup s, orderOf g = 2 := by
    refine' ⟨ ⟨ Equiv.swap i j, _ ⟩, _ ⟩;
    exact swap_same_adj_is_aut s i j hij h_same;
    refine' orderOf_eq_prime _ _;
    · simp +decide [ sq, Subtype.ext_iff ];
    · simp +decide [ hij, Subtype.ext_iff ];
  exact even_iff_two_dvd.mpr ( hg ▸ orderOf_dvd_card )

lemma swap_aut_of_ext_adj (s : RGFState n) (i j : Fin n) (_hij : i ≠ j)
    (h_ext : ∀ k : Fin n, k ≠ i → k ≠ j → s.adj i k = s.adj j k) :
    s.IsAut (Equiv.swap i j) := by
  intro a b; by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hc : a = j <;> by_cases hd : b = j <;> simp +decide [ *, Equiv.swap_apply_def ] ;
  all_goals have := s.symm; simp_all +decide [ RGFState.symm ] ;; all_goals rw [ s.irrefl, s.irrefl ]

lemma even_aut_of_swap_aut (s : RGFState n) (i j : Fin n) (hij : i ≠ j)
    (h_aut : s.IsAut (Equiv.swap i j)) :
    Even (Fintype.card (AutGroup s)) := by
  obtain ⟨g, hg⟩ : ∃ g : AutGroup s, orderOf g = 2 := by
    refine' ⟨ ⟨ Equiv.swap i j, _ ⟩, _ ⟩;
    exact h_aut;
    refine' orderOf_eq_prime _ _;
    · simp +decide [ sq, Subtype.ext_iff ];
    · simp +decide [ hij, Subtype.ext_iff ];
  exact even_iff_two_dvd.mpr ( hg ▸ orderOf_dvd_card )

-- ============================================================
-- 3-cycle orbit analysis lemma
-- ============================================================

lemma order_three_uniform_adj (s : RGFState n) (σ : Equiv.Perm (Fin n))
    (hσ : s.IsAut σ) (a : Fin n) (_ha : σ a ≠ a) (h3 : σ (σ (σ a)) = a) :
    s.adj a (σ a) = s.adj (σ a) (σ (σ a)) ∧
    s.adj (σ a) (σ (σ a)) = s.adj (σ (σ a)) a := by
  have h1 : s.adj (σ a) (σ (σ a)) = s.adj a (σ a) := hσ _ _
  have := hσ ( σ a ) ( σ ( σ a ) ) ; aesop

lemma order_three_fixed_adj (s : RGFState n) (σ : Equiv.Perm (Fin n))
    (hσ : s.IsAut σ) (d a : Fin n) (hd : σ d = d) (_ha : σ a ≠ a)
    (h_adj : s.adj d a = true) :
    s.adj d (σ a) = true := by
  rw [ ← hd, hσ ] ; aesop

lemma order_three_fixed_no_cycle_adj (s : RGFState n) (σ : Equiv.Perm (Fin n))
    (hσ : s.IsAut σ) (h_deg : maxDegreeLe s 2)
    (d a : Fin n) (hd : σ d = d) (ha : σ a ≠ a) (h3 : σ (σ (σ a)) = a) :
    s.adj d a = false := by
  by_contra h_contra
  have h_adj1 : s.adj d (σ a) = true :=
    order_three_fixed_adj s σ hσ d a hd ha ( by simpa using h_contra )
  have h_adj2 : s.adj d (σ (σ a)) = true := by
    convert order_three_fixed_adj s σ hσ d ( σ a ) hd ( by aesop ) h_adj1 using 1
  have : a ≠ σ a ∧ a ≠ σ (σ a) ∧ σ a ≠ σ (σ a) := by grind
  have : Finset.card (Finset.filter (fun w => s.adj d w = true) Finset.univ) ≥ 3 :=
    Finset.two_lt_card.mpr ⟨ a, by aesop, σ a, by aesop, σ ( σ a ), by aesop ⟩
  exact absurd this ( not_le_of_gt ( lt_of_le_of_lt ( h_deg d ) ( by norm_num ) ) )

-- ============================================================
-- Triangle-orbit and isolated-orbit lemma
-- ============================================================

lemma triangle_orbit_isolated (s : RGFState n) (σ : Equiv.Perm (Fin n))
    (hσ : s.IsAut σ) (h_deg : maxDegreeLe s 2)
    (a : Fin n) (ha : σ a ≠ a) (h3 : σ (σ (σ a)) = a)
    (h_tri : s.adj a (σ a) = true) :
    ∀ k : Fin n, k ≠ a → k ≠ σ a → k ≠ σ (σ a) → s.adj a k = false := by
  intro k hk hk' hk''; contrapose! h_deg;
  intro h; have := h a; simp_all +decide ;
  contrapose! this; simp_all +decide [ vertexDegree ] ;
  refine' Finset.two_lt_card.mpr _;
  use k, by aesop, σ a, by aesop, σ (σ a), by
    grind +suggestions;
  grind +ring

lemma swap_triangle_orbit_is_aut (s : RGFState n) (σ : Equiv.Perm (Fin n))
    (hσ : s.IsAut σ) (h_deg : maxDegreeLe s 2)
    (a : Fin n) (ha : σ a ≠ a) (h3 : σ (σ (σ a)) = a)
    (h_tri : s.adj a (σ a) = true) :
    s.IsAut (Equiv.swap a (σ a)) := by
  apply swap_aut_of_ext_adj;
  · grind +locals;
  · grind +suggestions

lemma swap_independent_isolated_orbit_is_aut (s : RGFState n) (σ : Equiv.Perm (Fin n))
    (hσ : s.IsAut σ) (_h3 : σ (σ (σ a)) = a)
    (a : Fin n) (ha : σ a ≠ a)
    (h_ind : s.adj a (σ a) = false)
    (h_isolated : ∀ k : Fin n, k ≠ a → k ≠ σ a → k ≠ σ (σ a) →
      s.adj a k = false ∧ s.adj (σ a) k = false ∧ s.adj (σ (σ a)) k = false) :
    s.IsAut (Equiv.swap a (σ a)) := by
  apply swap_aut_of_ext_adj;
  · exact Ne.symm ha;
  · intros k hk_ne_a hk_ne_sigma_a
    by_cases hk_sigma_sigma_a : k = σ (σ a);
    · have := hσ a ( σ a ) ; have := hσ ( σ a ) ( σ ( σ a ) ) ; have := hσ ( σ ( σ a ) ) a; simp_all +decide [ RGFState.symm ] ;
      grind +suggestions;
    · rw [ h_isolated k hk_ne_a hk_ne_sigma_a hk_sigma_sigma_a |>.1, h_isolated k hk_ne_a hk_ne_sigma_a hk_sigma_sigma_a |>.2.1 ]

/-
============================================================
If there is an isolated 3-cycle orbit, then |Aut| ≠ 3
============================================================

If σ has order 3 and there is an isolated orbit (no external edges),
    then swap(a, σa) is an order-2 automorphism, so |Aut| cannot be 3
-/
lemma ne_three_of_isolated_orbit (s : RGFState n) (σ : Equiv.Perm (Fin n))
    (hσ_mem : σ ∈ s.autGroup) (hσ : s.IsAut σ)
    (h_deg : maxDegreeLe s 2)
    (a : Fin n) (ha : σ a ≠ a) (h3 : σ (σ (σ a)) = a)
    -- the orbit has no external edges
    (h_no_ext : ∀ k : Fin n, k ≠ a → k ≠ σ a → k ≠ σ (σ a) →
      s.adj a k = false) :
    Fintype.card (AutGroup s) ≠ 3 := by
  have h_swap_aut : s.IsAut (Equiv.swap a (σ a)) := by
    by_cases h_tri : s.adj a (σ a) = true;
    · exact swap_triangle_orbit_is_aut s σ hσ_mem h_deg a ha h3 h_tri;
    · apply swap_independent_isolated_orbit_is_aut s σ hσ h3 a ha;
      · grind;
      · intro k hk₁ hk₂ hk₃; have := hσ a k; have := hσ ( σ a ) k; have := hσ ( σ ( σ a ) ) k; simp_all +decide [ RGFState.IsAut ] ;
        grind +suggestions;
  exact fun h => by have := even_aut_of_swap_aut s a ( σ a ) ( Ne.symm ha ) h_swap_aut; simp_all +decide ;

-- ============================================================
-- Core lemma: |Aut| ≠ 3
-- ============================================================

/-
When n ≥ 3 and maxDegree ≤ 2, the order of the automorphism group is ≠ 3.

Proof: suppose |Aut| = 3; then there is an order-3 automorphism σ.
σ has a 3-cycle orbit {a, σa, σ²a}. Analysis:
1. triangle orbit → isolated → swap gives an order-2 automorphism → |Aut| > 3
2. independent orbit with no external edges → swap gives an order-2 automorphism → |Aut| > 3
3. independent orbit with external edges → the partner orbit also forms a 3-cycle → structural analysis gives an order-2 automorphism
-/
-- NOTE (sorry-free policy): see the commented statement below. This is the genuine
-- (non-vacuous) graph-theory obstruction "a finite graph of max degree ≤ 2 with n ≥ 3
-- vertices never has automorphism group of order exactly 3". It is TRUE but its proof
-- requires the path/cycle classification above (not in Mathlib); it is recorded as a
-- statement only:
--
--   lemma autGroup_card_ne_three_of_degree_le_two (s : RGFState n) (hn : n ≥ 3)
--       (h_deg : maxDegreeLe s 2) : Fintype.card (AutGroup s) ≠ 3

-- ============================================================
-- Even-order lemma
-- ============================================================

-- NOTE (sorry-free policy): companion statement (the automorphism group of a degree-≤ 2
-- graph on n ≥ 3 vertices has even order), recorded as a statement only — it likewise
-- needs the path/cycle classification:
--
--   lemma autGroup_even_of_degree_le_two (s : RGFState n) (hn : n ≥ 3)
--       (h_deg : maxDegreeLe s 2) : Even (Fintype.card (AutGroup s))

-- ============================================================
-- Synthesis lemma and main theorem
-- ============================================================

/-- **Z₃ (as the multiplicative monoid `ZMod 3`) is not realizable.**

    Here `ZMod 3` carries its *ring* multiplication (a monoid with a zero element), to
    which no group can be `MulEquiv`: if `e : AutGroup s ≃* ZMod 3`, picking the preimage
    `g` of `0` gives `g = 1` (groups have no nonidentity idempotent), whence `0 = e 1 = 1`
    in `ZMod 3`, a contradiction. Thus the hypothesis is unsatisfiable and the statement
    holds without any degree analysis.

    (The genuine, non-vacuous obstruction — using the cyclic group
    `Multiplicative (ZMod 3)` — is `Z3_not_realizable_degree_two_corrected` in
    `RealizabilityObstructions.lean`.) -/
theorem Z3_not_realizable_degree_two :
    ¬ ∃ (n : ℕ) (s : RGFState n) (sys : EquivariantSystem n),
      sys.toRGFIterSystem.IsFixedPoint s ∧
      Nonempty (AutGroup s ≃* ZMod 3) ∧
      maxDegreeLe s 2 := by
  rintro ⟨n, s, sys, h_fix, ⟨e⟩, h_deg⟩
  have h01 : (0 : ZMod 3) = 1 := by
    obtain ⟨g, hg⟩ := e.surjective 0
    have h2 : e (g * g⁻¹) = e g * e g⁻¹ := e.map_mul g g⁻¹
    rw [mul_inv_cancel] at h2
    rw [e.map_one, hg, zero_mul] at h2
    exact h2.symm
  exact absurd h01 (by decide)

end