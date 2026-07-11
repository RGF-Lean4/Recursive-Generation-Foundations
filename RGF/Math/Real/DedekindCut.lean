/-
  RGF generative real-number system — Dedekind-cut construction
  Within the dual-layer iteration axiom framework, the reals are constructed from the rationals ℚ via Dedekind cuts.
-/

import Mathlib

open Set

namespace RGF.Real

/-- A Dedekind cut. -/
structure DedekindCut where
  carrier : Set ℚ
  nonempty : carrier.Nonempty
  ne_univ : carrier ≠ univ
  down_closed : ∀ p q : ℚ, p ≤ q → q ∈ carrier → p ∈ carrier
  no_max : ∀ q ∈ carrier, ∃ r ∈ carrier, q < r

theorem DedekindCut.ext {α β : DedekindCut} (h : α.carrier = β.carrier) : α = β := by
  cases α; cases β; simp_all

/-! ## Embedding of the rationals -/

def ofRat (q : ℚ) : DedekindCut where
  carrier := {p : ℚ | p < q}
  nonempty := ⟨q - 1, by simp⟩
  ne_univ := by
    intro h
    have : q ∈ ({p : ℚ | p < q} : Set ℚ) := by rw [h]; exact mem_univ q
    simp at this
  down_closed := fun p r hpr hr => lt_of_le_of_lt hpr hr
  no_max := by
    intro r hr; simp only [mem_setOf_eq] at hr ⊢
    exact ⟨(r + q) / 2, by linarith, by linarith⟩

theorem ofRat_injective : Function.Injective ofRat := by
  intro a b h
  simp only [ofRat, DedekindCut.mk.injEq] at h
  by_contra hab
  rcases ne_iff_lt_or_gt.mp hab with ha | ha
  · have : a ∈ ({p : ℚ | p < b} : Set ℚ) := ha; rw [← h] at this; simp at this
  · have : b ∈ ({p : ℚ | p < a} : Set ℚ) := ha; rw [h] at this; simp at this

/-! ## Order relation -/

instance : LE DedekindCut where le α β := α.carrier ⊆ β.carrier
instance : LT DedekindCut where lt α β := α.carrier ⊂ β.carrier

theorem le_refl' (α : DedekindCut) : α ≤ α := Subset.refl _

theorem le_trans' {α β γ : DedekindCut} (h₁ : α ≤ β) (h₂ : β ≤ γ) : α ≤ γ :=
  Subset.trans h₁ h₂

theorem le_antisymm' {α β : DedekindCut} (h₁ : α ≤ β) (h₂ : β ≤ α) : α = β :=
  DedekindCut.ext (Subset.antisymm h₁ h₂)

/-! ## Auxiliary lemmas -/

theorem not_mem_is_upper (α : DedekindCut) (q : ℚ) (hq : q ∉ α.carrier) :
    ∀ a ∈ α.carrier, a < q := by
  intro a ha; by_contra h; push_neg at h; exact hq (α.down_closed q a h ha)

theorem exists_not_mem (α : DedekindCut) : ∃ x, x ∉ α.carrier := by
  by_contra h'; push_neg at h'; exact α.ne_univ (eq_univ_of_forall h')

/-! ## Addition -/

def add (α β : DedekindCut) : DedekindCut where
  carrier := {q : ℚ | ∃ a ∈ α.carrier, ∃ b ∈ β.carrier, q = a + b}
  nonempty := by
    obtain ⟨a, ha⟩ := α.nonempty; obtain ⟨b, hb⟩ := β.nonempty
    exact ⟨a + b, a, ha, b, hb, rfl⟩
  ne_univ := by
    intro h
    obtain ⟨qa, hqa⟩ := exists_not_mem α; obtain ⟨qb, hqb⟩ := exists_not_mem β
    have : qa + qb ∈ ({q : ℚ | ∃ a ∈ α.carrier, ∃ b ∈ β.carrier, q = a + b} : Set ℚ) := by
      rw [h]; exact mem_univ _
    obtain ⟨a, ha, b, hb, hab⟩ := this
    linarith [not_mem_is_upper α qa hqa a ha, not_mem_is_upper β qb hqb b hb]
  down_closed := by
    intro p q hpq ⟨a, ha, b, hb, hq⟩
    exact ⟨a - (q - p), α.down_closed _ a (by linarith) ha, b, hb, by linarith⟩
  no_max := by
    intro q ⟨a, ha, b, hb, hq⟩
    obtain ⟨a', ha', haa'⟩ := α.no_max a ha
    exact ⟨a' + b, ⟨a', ha', b, hb, rfl⟩, by linarith⟩

instance : Add DedekindCut where add := add

theorem add_comm' (α β : DedekindCut) : α + β = β + α := by
  apply DedekindCut.ext; ext q
  show (∃ a ∈ α.carrier, ∃ b ∈ β.carrier, q = a + b) ↔
       (∃ a ∈ β.carrier, ∃ b ∈ α.carrier, q = a + b)
  exact ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨b, hb, a, ha, by linarith⟩,
         fun ⟨b, hb, a, ha, h⟩ => ⟨a, ha, b, hb, by linarith⟩⟩

/-! ## Supremum property (completeness) -/

private theorem mem_sup_carrier (S : Set DedekindCut) (q : ℚ) :
    q ∈ (⋃ α ∈ S, α.carrier) ↔ ∃ α ∈ S, q ∈ α.carrier := by
  simp [mem_iUnion]

def sup' (S : Set DedekindCut) (hne : S.Nonempty) (hbdd : ∃ β, ∀ α ∈ S, α ≤ β) :
    DedekindCut where
  carrier := ⋃ α ∈ S, α.carrier
  nonempty := by
    obtain ⟨α, hα⟩ := hne; obtain ⟨q, hq⟩ := α.nonempty
    exact ⟨q, (mem_sup_carrier S q).mpr ⟨α, hα, hq⟩⟩
  ne_univ := by
    obtain ⟨β, hβ⟩ := hbdd; obtain ⟨q, hq⟩ := exists_not_mem β
    intro heq; apply hq
    obtain ⟨α, hα, hqα⟩ := (mem_sup_carrier S q).mp (heq ▸ mem_univ q)
    exact hβ α hα hqα
  down_closed := by
    intro p q hpq hq
    obtain ⟨α, hα, hqα⟩ := (mem_sup_carrier S q).mp hq
    exact (mem_sup_carrier S p).mpr ⟨α, hα, α.down_closed p q hpq hqα⟩
  no_max := by
    intro q hq
    obtain ⟨α, hα, hqα⟩ := (mem_sup_carrier S q).mp hq
    obtain ⟨r, hr, hqr⟩ := α.no_max q hqα
    exact ⟨r, (mem_sup_carrier S r).mpr ⟨α, hα, hr⟩, hqr⟩

theorem le_sup' (S : Set DedekindCut) (hne : S.Nonempty)
    (hbdd : ∃ β, ∀ α ∈ S, α ≤ β) (α : DedekindCut) (hα : α ∈ S) :
    α ≤ sup' S hne hbdd :=
  fun _ hq => (mem_sup_carrier S _).mpr ⟨α, hα, hq⟩

theorem sup_le' (S : Set DedekindCut) (hne : S.Nonempty)
    (hbdd : ∃ β, ∀ α ∈ S, α ≤ β) (β : DedekindCut) (hβ : ∀ α ∈ S, α ≤ β) :
    sup' S hne hbdd ≤ β := by
  intro q hq
  obtain ⟨α, hα, hqα⟩ := (mem_sup_carrier S q).mp hq
  exact hβ α hα hqα

/-! ## Total order -/

theorem le_total' (α β : DedekindCut) : α ≤ β ∨ β ≤ α := by
  suffices h : α.carrier ⊆ β.carrier ∨ β.carrier ⊆ α.carrier from h
  by_contra h; rw [not_or] at h
  obtain ⟨q₁, hq₁_mem, hq₁_not⟩ := Set.not_subset.mp h.1
  obtain ⟨q₂, hq₂_mem, hq₂_not⟩ := Set.not_subset.mp h.2
  linarith [not_mem_is_upper α q₂ hq₂_not q₁ hq₁_mem,
            not_mem_is_upper β q₁ hq₁_not q₂ hq₂_mem]

/-! ## Connection with RGF dual-layer iteration -/

theorem dedekind_as_rgf_fixpoint (α : DedekindCut) :
    ∀ q ∈ α.carrier, ∃ r ∈ α.carrier, q < r := α.no_max

theorem rat_dense_in_cuts (α β : DedekindCut) (h : α < β) :
    ∃ q : ℚ, q ∉ α.carrier ∧ q ∈ β.carrier := by
  have hsub : α.carrier ⊆ β.carrier := h.subset
  have hne : α.carrier ≠ β.carrier := h.ne
  have : ∃ x, x ∈ β.carrier ∧ x ∉ α.carrier := by
    by_contra h'; push_neg at h'
    exact hne (Subset.antisymm hsub (fun x hx => h' x hx))
  obtain ⟨q, hq1, hq2⟩ := this; exact ⟨q, hq2, hq1⟩

end RGF.Real
