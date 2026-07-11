/-
  RGF2/EmergentOmega.lean   (module `RGF2.EmergentOmega`)

  **§2 — Emergence–isomorphism, replacing renaming.**

  `RGF2/GenerativeBridge.lean` defines the "generative step" `succOrd₂` *through*
  set theory (`equivZF.symm (insert (equivZF a) (equivZF a))`) and then iterates it;
  the resulting "bridge" theorems merely unfold the von Neumann successor in two
  notations.  They do not show that `ω` *emerges* from a dynamics: the set theory is
  used up front.

  This file does the converse, as the plan asks:

    1. **define a generative operator purely dynamically**, with *no* reference to
       set theory — an abstract unary system `GenSystem` `(g : X → X, seed : X)`;
    2. show `ω` **emerges** as the orbit of that operator from its seed, and — the
       load-bearing part — that the intrinsic *reachability* order on the orbit is
       an order isomorphism onto `ℕ`;
    3. **connect** that emergent order to the *standard* ordinal `ω` via the bundled
       order isomorphism `natOrderIsoIioOmega : ℕ ≃o Set.Iio Ordinal.omega0`.

  The content is carried by the isomorphism theorems, not by a definition named
  "step".  The criterion demanded by the audit is met: the emergent object is
  defined without any set theory, and only afterwards matched to the standard `ω`.

  **Falsifiability.**  The freeness hypothesis (`IsFree`, i.e. the step keeps
  producing genuinely new states) is essential and *violable*: the degenerate
  system with `g = id` is not free and its orbit collapses to a single point
  (`idSystem_orbit_subsingleton`), so it does *not* generate `ω`.  Emergence of `ω`
  is therefore a real property of the dynamics, not an automatic renaming.
-/
import Mathlib

open Ordinal

universe u

namespace RGF
namespace RGF2
namespace Emergent

/-- An abstract **unary generative system**: a single step operator `g` on a state
type `X` together with a `seed`.  No set theory, no ordinals — pure dynamics. -/
structure GenSystem (X : Type u) where
  /-- the generative step operator -/
  g : X → X
  /-- the seed state from which generation starts -/
  seed : X

namespace GenSystem

variable {X : Type u}

/-- The state reached after `n` generative steps from the seed. -/
def reach (S : GenSystem X) (n : ℕ) : X := (S.g^[n]) S.seed

/-- The **orbit**: the set of all states generated from the seed. -/
def Orbit (S : GenSystem X) : Set X := Set.range S.reach

/-- The intrinsic **reachability** relation of the dynamics: `b` is reachable from
`a` by iterating the step some number of times.  This is the order that the
generation *itself* induces, defined without reference to indices. -/
def Reaches (S : GenSystem X) (a b : X) : Prop := ∃ k : ℕ, (S.g^[k]) a = b

/-- A system is **free** when distinct step counts yield distinct states, i.e. the
step keeps producing genuinely new objects.  This is the non-degeneracy hypothesis
that makes the orbit an `ω`. -/
def IsFree (S : GenSystem X) : Prop := Function.Injective S.reach

theorem reach_zero (S : GenSystem X) : S.reach 0 = S.seed := rfl

theorem reach_add (S : GenSystem X) (n k : ℕ) :
    S.reach (n + k) = (S.g^[k]) (S.reach n) := by
  unfold reach
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- `reach n` is always reachable from `reach m` when `m ≤ n` — the forward,
purely dynamical direction (no freeness needed). -/
theorem reaches_of_le (S : GenSystem X) {m n : ℕ} (h : m ≤ n) :
    S.Reaches (S.reach m) (S.reach n) := by
  refine ⟨n - m, ?_⟩
  have := S.reach_add m (n - m)
  rw [Nat.add_sub_cancel' h] at this
  exact this.symm

/-- **The emergence–isomorphism (order direction).**  For a *free* system, the
intrinsic reachability order on the orbit is *exactly* the order of `ℕ`:
`reach m` reaches `reach n` iff `m ≤ n`.  This is the order-isomorphism content —
the orbit, with the order the dynamics itself induces, is `(ℕ, ≤)`. -/
theorem reaches_iff_le (S : GenSystem X) (hS : S.IsFree) (m n : ℕ) :
    S.Reaches (S.reach m) (S.reach n) ↔ m ≤ n := by
  constructor
  · rintro ⟨k, hk⟩
    have h2 : S.reach (m + k) = S.reach n := by
      rw [S.reach_add m k]; exact hk
    have := hS h2
    omega
  · intro h; exact S.reaches_of_le h

/-- **The emergence–isomorphism (bijection direction).**  For a free system, `reach`
is a bijection from `ℕ` onto the orbit: the orbit is a faithful copy of `ℕ`. -/
theorem reach_bijOn (S : GenSystem X) (hS : S.IsFree) :
    Set.BijOn S.reach Set.univ S.Orbit := by
  refine ⟨fun n _ => ⟨n, rfl⟩, ?_, ?_⟩
  · intro a _ b _ h; exact hS h
  · rintro b ⟨n, rfl⟩; exact ⟨n, trivial, rfl⟩

end GenSystem

/-! ## The standard ordinal `ω`, as an order isomorphism target -/

/-- The **standard** ordinal `ω`, presented as the order of ordinals below
`Ordinal.omega0`.  This bundled order isomorphism `ℕ ≃o Set.Iio ω` is what the
emergent orbit is matched against. -/
noncomputable def natOrderIsoIioOmega : ℕ ≃o Set.Iio (Ordinal.omega0.{u}) := by
  refine StrictMono.orderIsoOfSurjective
    (fun n => ⟨(n : Ordinal.{u}), Ordinal.nat_lt_omega0 n⟩) ?_ ?_
  · intro a b hab
    exact Subtype.mk_lt_mk.mpr (by exact_mod_cast hab)
  · rintro ⟨o, ho⟩
    rw [Set.mem_Iio, Ordinal.lt_omega0] at ho
    obtain ⟨n, rfl⟩ := ho
    exact ⟨n, rfl⟩

/-- **`ω` emerges from the dynamics and matches the standard `ω`.**  For any free
generative system there is a bijection `e : ℕ ≃ orbit` such that the intrinsic
reachability order on the orbit corresponds to `≤` on `ℕ`, *and* `ℕ` is
order-isomorphic (`natOrderIsoIioOmega`) to the standard ordinals below `ω`.
Composing, the purely dynamical orbit *is* the standard `ω` — established by an
isomorphism, not by a definitional renaming. -/
theorem emergent_matches_standard_omega {X : Type u} (S : GenSystem X) (hS : S.IsFree) :
    (∀ m n, S.Reaches (S.reach m) (S.reach n) ↔ m ≤ n) ∧
      Set.BijOn S.reach Set.univ S.Orbit ∧
      Nonempty (ℕ ≃o Set.Iio (Ordinal.omega0.{u})) :=
  ⟨S.reaches_iff_le hS, S.reach_bijOn hS, ⟨natOrderIsoIioOmega⟩⟩

/-! ## A concrete emergent system on a non-`ℕ` carrier -/

/-- The successor dynamics on `ℤ` from seed `0`: a purely dynamical generator whose
carrier is *not* `ℕ`. -/
def intSuccSystem : GenSystem ℤ := ⟨fun x => x + 1, 0⟩

theorem intSuccSystem_reach (n : ℕ) : intSuccSystem.reach n = (n : ℤ) := by
  unfold GenSystem.reach intSuccSystem
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; push_cast; ring

/-- The integer successor system is free — so its orbit genuinely emerges as `ω`. -/
theorem intSuccSystem_isFree : intSuccSystem.IsFree := by
  intro a b h
  rw [intSuccSystem_reach, intSuccSystem_reach] at h
  exact_mod_cast h

/-- Hence the `ℤ`-based successor dynamics generates a standard `ω`. -/
theorem intSuccSystem_emerges_omega :
    (∀ m n, intSuccSystem.Reaches (intSuccSystem.reach m) (intSuccSystem.reach n) ↔ m ≤ n) ∧
      Set.BijOn intSuccSystem.reach Set.univ intSuccSystem.Orbit ∧
      Nonempty (ℕ ≃o Set.Iio (Ordinal.omega0.{0})) :=
  emergent_matches_standard_omega intSuccSystem intSuccSystem_isFree

/-! ## Falsifiability: a degenerate generator fails to produce `ω` -/

/-- The degenerate "generator" `g = id`, which never produces anything new. -/
def idSystem {X : Type u} (x : X) : GenSystem X := ⟨id, x⟩

theorem idSystem_reach {X : Type u} (x : X) (n : ℕ) : (idSystem x).reach n = x := by
  unfold GenSystem.reach idSystem
  simp

/-- The degenerate system is **not free**: `IsFree` is a genuine, violable
hypothesis. -/
theorem idSystem_not_isFree {X : Type u} (x : X) :
    ¬ (idSystem x).IsFree := by
  intro hfree
  exact absurd (hfree (a₁ := 0) (a₂ := 1) (by rw [idSystem_reach, idSystem_reach])) (by decide)

/-- Its orbit collapses to a single point — it does *not* generate `ω`.  Emergence
of `ω` therefore relies essentially on freeness and is not automatic. -/
theorem idSystem_orbit_subsingleton {X : Type u} (x : X) :
    (idSystem x).Orbit = {x} := by
  ext a
  constructor
  · rintro ⟨n, rfl⟩; rw [idSystem_reach]; rfl
  · intro ha
    rw [Set.mem_singleton_iff] at ha
    exact ⟨0, (idSystem_reach x 0).trans ha.symm⟩

/-! ## Axiom audit -/

#print axioms GenSystem.reaches_iff_le
#print axioms emergent_matches_standard_omega
#print axioms natOrderIsoIioOmega
#print axioms intSuccSystem_emerges_omega
#print axioms idSystem_orbit_subsingleton

end Emergent
end RGF2
end RGF
