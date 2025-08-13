import MyLean.MetricSpaces.Basic

open Topology

namespace Diam

variable {α : Type} [Metric α]

/-
  ### Limited space
-/
def isLimited (s : Set α) :=
  ∃ d : ℝ, ∀ x ∈ s, ∀ y ∈ s, dist x y < d

/-
  ### Diam
-/
noncomputable def diam (s : Set α) : ℝ := sorry


variable (s : Set α)

theorem diam_to_radius : ∀ x ∈ s, s ⊆ ball x (diam s) := by
  intro x hx y hy
  rw [mem_ball, diam]
  sorry

end Diam
