import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set

namespace Topology
variable {α : Type} {s₁ s₂ t₁ t₂ : Set α}

class TopologicalSpace (a: Type) where
  isOpen : Set a → Prop
  isOpen_empty  : isOpen ∅
  isOpen_univ : isOpen univ
  isOpen_inter : ∀ s t, isOpen s → isOpen t → isOpen (s ∩ t)
  isOpen_union : ∀ s t, isOpen s → isOpen t → isOpen (s ∪ t)

def isOpen [TopologicalSpace α] : Set α → Prop :=
  TopologicalSpace.isOpen

def isOpen_empty [TopologicalSpace α] : isOpen (∅ : Set α) :=
  TopologicalSpace.isOpen_empty

def isOpen_univ [TopologicalSpace α] : isOpen (univ : Set α) :=
  TopologicalSpace.isOpen_univ

def isOpen_inter [TopologicalSpace α] (h₁ : isOpen s₁) (h₂ : isOpen s₂) : isOpen (s₁ ∩ s₂) :=
  TopologicalSpace.isOpen_inter s₁ s₂ h₁ h₂

def isOpen_union [TopologicalSpace α] (h₁ : isOpen s₁) (h₂ : isOpen s₂) : isOpen (s₁ ∪ s₂) :=
  TopologicalSpace.isOpen_union s₁ s₂ h₁ h₂

@[simp]
instance : LT (TopologicalSpace α) where
  lt s t := ∀ (a : Set α), s.isOpen a → t.isOpen a

variable [TopologicalSpace α]

/-
  ### Closed sets
-/

class isClosed (s : Set α) : Prop where
  isOpen_compl : isOpen sᶜ

@[simp] theorem isOpen_compl_iff {s : Set α} : isOpen sᶜ ↔ isClosed s :=
  ⟨fun h => ⟨h⟩, fun h => h.isOpen_compl⟩

@[simp] theorem isClosed_empty : isClosed (∅ : Set α) := by
  have h_eq : (∅ᶜ : Set α) = (univ : Set α) := by ext; simp
  have h_open : isOpen (∅ᶜ : Set α) := by
    rw [h_eq]
    exact isOpen_univ
  apply isOpen_compl_iff.1
  exact h_open

@[simp] theorem isClosed_univ : isClosed (univ : Set α) := by
  have h_eq : (univᶜ : Set α) = (∅ : Set α) := by ext; simp
  apply isOpen_compl_iff.1
  rw [h_eq]
  exact isOpen_empty

@[simp] theorem isClosed_inter : isClosed s₁ → isClosed s₂ → isClosed (s₁ ∩ s₂) := by
  simpa only [← isOpen_compl_iff, compl_inter] using isOpen_union

@[simp] theorem isClosed_union : isClosed s₁ → isClosed s₂ → isClosed (s₁ ∪ s₂) := by
  simpa only [← isOpen_compl_iff, compl_union] using isOpen_inter

/-
  ### Neighborhoods
-/

def nhds (a : α) := {s : Set α | a ∈ s ∧ isOpen s}

/-
  ### Basis of the topology
-/

class TopologicalBasis (s : Set (Set α)) where
  basis_full := ⋃₀ s = univ
  basis_axiom := ∀ t₁ ∈ s, ∀ t₂ ∈ s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃ ∈ s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂

end Topology
