import MyLean.MetricSpaces

open Topology

namespace test

variable {X : Type} [DecidableEq X]

@[simp] def dist_fun₁ (x y : X) : ℝ :=
  if x = y then 0
  else 1

instance : Topology.Metric X where
  dist := dist_fun₁
  dist_self := by simp
  dist_comm := by
    intro x y
    simp
    by_cases h : x = y
    · rw [h]
    · have h' : y ≠ x := by symm; exact h
      simp [h', h]
  dist_triangle := by
    intro x y z
    simp
    by_cases h₁ : x = y
    · by_cases h₂ : y = z
      · simp [h₁, h₂]
      · push_neg at h₂
        simp [h₁, h₂, h₂.symm]
    · by_cases h₂ : y = z
      · push_neg at h₁
        simp [h₂]
      · by_cases h₃ : x = z
        · simp [h₃]
        · push_neg at h₁ h₂ h₃
          rw [if_neg h₁, if_neg h₂.symm, if_neg h₃]
          linarith
  dist_eq := by
    intro x y h
    simp at h
    by_cases h' : x = y
    · exact h'
    · contradiction

@[simp] def dist_fun₂ (x y : ℝ) : ℝ := |x - y|

instance : Topology.Metric ℝ where
  dist := dist_fun₂
  dist_comm := by
    intro x y; simp; rw [abs_sub_comm]
  dist_self := by
    intro x; simp
  dist_triangle := by
    intro x y z; simp;
    rw [← add_zero (x-y), ← sub_self z, ← add_comm_sub, sub_right_comm]
    rw [add_comm_sub]
    exact abs_add (x-z) (z-y)
  dist_eq := by
    intro x y h
    simp at h
    rw [sub_eq_zero] at h
    exact h

end test
