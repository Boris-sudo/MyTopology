import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

open Topology Set Metric

variable {α : Type} [MetricSpace α]
variable (x y : α) (s : Set α)
variable (r : ℝ)

example : ball x (r - dist x y) ⊆ ball y r := by
  intro a ha
  apply mem_ball.1
  apply mem_ball.1 at ha
  apply lt_sub_iff_add_lt.1 at ha
  exact lt_of_le_of_lt (dist_triangle a x y) ha

example (h : r < dist x y) : ball x (dist x y - r) ∩ ball y r = ∅ := by
  ext a
  constructor
  · intro ⟨h₁, h₂⟩
    simp only [mem_ball] at h₁ h₂
    rw [mem_empty_iff_false]
    have h' : dist a x + dist a y < dist x y := calc
      dist a x + dist a y < dist x y - r + r := add_lt_add h₁ h₂
      _ = dist x y := by rw [sub_add_cancel]
    rw [dist_comm a x] at h'
    have := dist_triangle x a y
    exact not_le_of_gt h' this
  · intro h
    simp at h


example (s:Set α) : diam s
