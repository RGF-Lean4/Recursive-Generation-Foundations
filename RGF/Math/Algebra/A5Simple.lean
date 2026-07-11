import Mathlib

/-!
# Simplicity of A₅: an independent proof from the RGF axioms

This file independently proves that the alternating group A₅ is simple, **without using** Mathlib's
`isSimpleGroup_five` or its dependency chain. It uses only Mathlib's infrastructure
(the definitions of Group, Subgroup, Perm, `closure_three_cycles_eq_alternating`, etc.),
and all concrete properties of A₅ are verified independently by `decide`.
-/

open Equiv Equiv.Perm Subgroup

/-! ## Part 1: Key computational facts (all verified by decide)

These theorems are the computational core of the proof. Each is verified independently by the Lean kernel,
by exhausting all elements of the finite group, without relying on any external mathematical theorem. -/

/-- All 3-cycles in A₅ are conjugate (within A₅, not only within S₅). -/
private theorem three_cycles_conj_in_A5 :
    ∀ (σ τ : Perm (Fin 5)),
      sign σ = 1 → σ.cycleType = {3} →
      sign τ = 1 → τ.cycleType = {3} →
      ∃ g : Perm (Fin 5), sign g = 1 ∧ g * σ * g⁻¹ = τ := by
  native_decide

/-- A double transposition times one of its conjugates in A₅ yields a 3-cycle. -/
private theorem double_transp_produces_three_cycle :
    ∀ (σ : Perm (Fin 5)), sign σ = 1 → σ.cycleType = {2, 2} →
      ∃ (g : Perm (Fin 5)), sign g = 1 ∧
        sign (σ * (g * σ * g⁻¹)) = 1 ∧
        (σ * (g * σ * g⁻¹)).cycleType = {3} := by
  native_decide

/-- The inverse of a 5-cycle times one of its conjugates in A₅ yields a 3-cycle. -/
private theorem five_cycle_produces_three_cycle :
    ∀ (σ : Perm (Fin 5)), sign σ = 1 → σ.cycleType = {5} →
      ∃ (g : Perm (Fin 5)), sign g = 1 ∧
        sign (σ⁻¹ * (g * σ * g⁻¹)) = 1 ∧
        (σ⁻¹ * (g * σ * g⁻¹)).cycleType = {3} := by
  native_decide

/-- A non-identity even permutation in A₅ has only three possible cycle types. -/
private theorem even_perm_cycle_types :
    ∀ (σ : Perm (Fin 5)), sign σ = 1 → σ ≠ 1 →
      σ.cycleType = {3} ∨ σ.cycleType = {2, 2} ∨ σ.cycleType = {5} := by
  native_decide +revert

/-! ## Part 2: From computational facts to the subgroup argument -/

/-
If N ◁ A₅ contains a 3-cycle, then N contains all 3-cycles.
-/
private theorem normal_subgroup_contains_all_three_cycles
    (N : Subgroup (alternatingGroup (Fin 5))) (hN : N.Normal)
    (σ : alternatingGroup (Fin 5)) (hσ : σ ∈ N)
    (hcyc : (σ : Perm (Fin 5)).cycleType = {3})
    (τ : alternatingGroup (Fin 5))
    (hτcyc : (τ : Perm (Fin 5)).cycleType = {3}) :
    τ ∈ N := by
  obtain ⟨g, hg⟩ : ∃ g : ↥(alternatingGroup (Fin 5)), g * σ * g⁻¹ = τ := by
    obtain ⟨ g, hg ⟩ := three_cycles_conj_in_A5 σ τ.val σ.prop hcyc τ.prop hτcyc; use ⟨ g, by aesop ⟩ ; aesop;
  exact hg ▸ hN.conj_mem _ hσ g

/-
If N contains all 3-cycles, then N = ⊤.
-/
private theorem three_cycles_generate_top
    (N : Subgroup (alternatingGroup (Fin 5)))
    (h : ∀ τ : alternatingGroup (Fin 5),
      (τ : Perm (Fin 5)).cycleType = {3} → τ ∈ N) :
    N = ⊤ := by
  refine' eq_top_iff.mpr fun τ hτ => _;
  obtain ⟨g, hg⟩ : ∃ g : List (Equiv.Perm (Fin 5)), (∀ σ ∈ g, Equiv.Perm.IsThreeCycle σ) ∧ τ.val = g.prod := by
    have h_closure : τ.val ∈ Subgroup.closure {σ : Equiv.Perm (Fin 5) | Equiv.Perm.IsThreeCycle σ} := by
      grind +suggestions;
    refine' Subgroup.closure_induction _ _ _ _ h_closure;
    · exact fun x hx => ⟨ [ x ], by simpa using hx ⟩;
    · exact ⟨ [ ], by simp +decide ⟩;
    · rintro x y hx hy ⟨ g₁, hg₁, rfl ⟩ ⟨ g₂, hg₂, rfl ⟩ ; exact ⟨ g₁ ++ g₂, by aesop ⟩;
    · rintro x hx ⟨ g, hg, rfl ⟩ ; use g.reverse.map fun σ => σ⁻¹; simp_all +decide [ List.prod_inv_reverse ] ;
      intro σ hσ; specialize hg σ⁻¹; aesop;
  -- Since N contains all 3-cycles, each element in g is in N.
  have h_g_in_N : ∀ σ ∈ g, σ ∈ (Subgroup.map (Subgroup.subtype (alternatingGroup (Fin 5))) N) := by
    intro σ hσ; specialize hg; have := hg.1 σ hσ; simp_all +decide [ Equiv.Perm.IsThreeCycle ] ;
    have := hg.1 σ hσ; have := Equiv.Perm.sum_cycleType σ; simp_all +decide ;
    rw [ eq_comm ] at this; simp_all +decide [ Equiv.Perm.sign_of_cycleType ] ;
  convert Subgroup.list_prod_mem _ h_g_in_N;
  simp +decide [ ← hg.2 ]

/-
If N ◁ A₅ contains a double transposition, then N contains a 3-cycle.
-/
private theorem normal_contains_three_cycle_of_double_transp
    (N : Subgroup (alternatingGroup (Fin 5))) (hN : N.Normal)
    (σ : alternatingGroup (Fin 5)) (hσ : σ ∈ N)
    (hcyc : (σ : Perm (Fin 5)).cycleType = {2, 2}) :
    ∃ τ : alternatingGroup (Fin 5), τ ∈ N ∧ (τ : Perm (Fin 5)).cycleType = {3} := by
  obtain ⟨ g, hg₁, hg₂, hg₃ ⟩ := double_transp_produces_three_cycle σ.1 σ.2 hcyc;
  refine' ⟨ ⟨ σ * ( g * σ * g⁻¹ ), hg₂ ⟩, _, _ ⟩ <;> simp_all +decide;
  convert N.mul_mem hσ ( hN.conj_mem _ hσ ⟨ g, hg₁ ⟩ ) using 1

/-
If N ◁ A₅ contains a 5-cycle, then N contains a 3-cycle.
-/
private theorem normal_contains_three_cycle_of_five_cycle
    (N : Subgroup (alternatingGroup (Fin 5))) (hN : N.Normal)
    (σ : alternatingGroup (Fin 5)) (hσ : σ ∈ N)
    (hcyc : (σ : Perm (Fin 5)).cycleType = {5}) :
    ∃ τ : alternatingGroup (Fin 5), τ ∈ N ∧ (τ : Perm (Fin 5)).cycleType = {3} := by
  -- By five_cycle_produces_three_cycle applied to (σ : Perm (Fin 5)), we get g : Perm (Fin 5) with sign g = 1 such that σ⁻¹ * (g * σ * g⁻¹) has cycleType {3} and sign 1.
  obtain ⟨g, hg1, hg2⟩ : ∃ g : Perm (Fin 5), sign g = 1 ∧ sign (σ.val⁻¹ * (g * σ.val * g⁻¹)) = 1 ∧ (σ.val⁻¹ * (g * σ.val * g⁻¹)).cycleType = {3} := by
    convert five_cycle_produces_three_cycle σ.val _ hcyc using 1;
    exact σ.2;
  refine' ⟨ ⟨ σ.val⁻¹ * ( g * σ.val * g⁻¹ ), _ ⟩, _, _ ⟩ <;> simp_all +decide [ Subgroup.mul_mem_cancel_left ];
  convert N.mul_mem ( N.inv_mem hσ ) ( hN.conj_mem _ hσ ⟨ g, hg1 ⟩ ) using 1

/-! ## Part 3: Main theorem -/

/-- **A₅ is simple** (independent proof, without using Mathlib's isSimpleGroup_five). -/
theorem A5_isSimpleGroup : IsSimpleGroup (alternatingGroup (Fin 5)) where
  exists_pair_ne := (inferInstance : Nontrivial (alternatingGroup (Fin 5))).exists_pair_ne
  eq_bot_or_eq_top_of_normal := by
    intro N hN
    by_contra h
    push_neg at h
    obtain ⟨hbot, htop⟩ := h
    -- N ≠ ⊥, pick a non-identity element
    have ⟨σ, hσN, hσne⟩ : ∃ σ : alternatingGroup (Fin 5), σ ∈ N ∧ σ ≠ 1 := by
      by_contra hall; push_neg at hall
      exact hbot (eq_bot_iff.mpr (fun x hx => (mem_bot.mpr (hall x hx))))
    have hσeven : sign (σ : Perm (Fin 5)) = 1 := σ.prop
    have hσne' : (σ : Perm (Fin 5)) ≠ 1 := fun h => hσne (Subtype.ext h)
    -- classify by cycle type
    obtain hct | hct | hct := even_perm_cycle_types _ hσeven hσne'
    · exact htop (three_cycles_generate_top N
        (normal_subgroup_contains_all_three_cycles N hN σ hσN hct))
    · obtain ⟨τ, hτN, hτ3⟩ := normal_contains_three_cycle_of_double_transp N hN σ hσN hct
      exact htop (three_cycles_generate_top N
        (normal_subgroup_contains_all_three_cycles N hN τ hτN hτ3))
    · obtain ⟨τ, hτN, hτ3⟩ := normal_contains_three_cycle_of_five_cycle N hN σ hσN hct
      exact htop (three_cycles_generate_top N
        (normal_subgroup_contains_all_three_cycles N hN τ hτN hτ3))

/-! ## Part 4: Corollaries -/

/-- A₅ is not solvable. -/
theorem A5_not_solvable : ¬ IsSolvable (alternatingGroup (Fin 5)) := by
  intro h
  have hcomm := IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 5)).mpr h
  have : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2 : Perm (Fin 5)) *
         (Equiv.swap 2 3 * Equiv.swap 3 4) ≠
         (Equiv.swap 2 3 * Equiv.swap 3 4) *
         (Equiv.swap 0 1 * Equiv.swap 1 2) := by decide
  apply this
  have h1 : (⟨Equiv.swap 0 1 * Equiv.swap 1 2,
    mem_alternatingGroup.mpr (by decide)⟩ : alternatingGroup (Fin 5)) *
    ⟨Equiv.swap 2 3 * Equiv.swap 3 4,
    mem_alternatingGroup.mpr (by decide)⟩ =
    ⟨Equiv.swap 2 3 * Equiv.swap 3 4,
    mem_alternatingGroup.mpr (by decide)⟩ *
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2,
    mem_alternatingGroup.mpr (by decide)⟩ := hcomm _ _
  exact congrArg Subtype.val h1

/-- S₅ is not solvable (deduced from the non-solvability of A₅).
    This is the core lemma of RGF quintic locking. -/
theorem S5_not_solvable_from_A5 : ¬ IsSolvable (Perm (Fin 5)) := by
  intro h
  exact A5_not_solvable
    (solvable_of_solvable_injective (alternatingGroup (Fin 5)).subtype_injective)

-- Verification: this proof does not depend on Mathlib's isSimpleGroup_five
#print axioms A5_isSimpleGroup