/-
  RGFBasic.lean — Core RGF Axiomatic Structures

  Defines the fundamental structures of Recursive Generation Foundations:
  - RGF: the base system with atoms
  - RuleLayer: probability distributions on atoms (the "ancestor" layer)
  - DualLayerSystem: the dual-layer iteration system
-/

import Mathlib

open Finset BigOperators

/-- RGF (Theory of Recursive Generation) base structure.
    A finite nonempty set of atoms. -/
structure RGF where
  /-- The type of atoms -/
  Atom : Type
  /-- Atoms form a finite type -/
  atomFintype : Fintype Atom
  /-- At least one atom exists -/
  atomNonempty : Nonempty Atom

/-- RuleLayer: a probability distribution on a finite type α.
    Represents the "ancestor" layer in dual-layer iteration. -/
structure RuleLayer (α : Type) [Fintype α] where
  /-- Weight function (probability mass) -/
  weight : α → ℝ
  /-- All weights are non-negative -/
  weight_nonneg : ∀ a, 0 ≤ weight a
  /-- Weights sum to 1 (normalization) -/
  weight_sum : ∑ a : α, weight a = 1

namespace RuleLayer

variable {α : Type} [Fintype α]

/-- Each weight is at most 1. -/
theorem weight_le_one (r : RuleLayer α) (a : α) : r.weight a ≤ 1 := by
  have h := r.weight_sum
  have hle : r.weight a ≤ ∑ b : α, r.weight b :=
    Finset.single_le_sum (fun b _ => r.weight_nonneg b) (Finset.mem_univ a)
  linarith

end RuleLayer

/-- DualLayerSystem: the core dual-layer iteration system.
    `generate` maps a rule layer to an entity (offspring),
    `modify` maps an entity back to a rule layer. -/
structure DualLayerSystem (α : Type) [Fintype α] where
  /-- Initial rule layer -/
  ruleLayer : RuleLayer α
  /-- Generate entities from a rule layer -/
  generate : RuleLayer α → List α
  /-- Modify: produce a new rule layer from entities -/
  modify : List α → RuleLayer α

namespace DualLayerSystem

variable {α : Type} [Fintype α]

/-- One step of dual-layer iteration: generate then modify. -/
def step (sys : DualLayerSystem α) (r : RuleLayer α) : RuleLayer α :=
  sys.modify (sys.generate r)

/-- Iterate the dual-layer step n times. -/
def iterate (sys : DualLayerSystem α) (r : RuleLayer α) : ℕ → RuleLayer α
  | 0 => r
  | n + 1 => sys.step (sys.iterate r n)

/-- A rule layer is a fixed point if one step leaves it unchanged. -/
def IsFixedPoint (sys : DualLayerSystem α) (r : RuleLayer α) : Prop :=
  sys.step r = r

end DualLayerSystem
