import MyLean.MetricSpaces.Diam

open Topology Diam

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

variable {α : Type} [Metric α]

example (x a : α) (r : ℝ) (h : r > dist x a) : ball x (r - dist x a) ⊆ ball a r := by
  intro y hy
  simp only [mem_ball] at hy ⊢
  apply lt_sub_iff_add_lt.1 at hy
  exact lt_of_le_of_lt (Topology.dist_triangle y a x) hy

example (s : Set α) (h : s.Nonempty) : isLimited s ↔ ∃ r : ℝ, ∃ x ∈ s, s ⊆ ball x r := by
  rw [isLimited]
  constructor
  · rintro ⟨d, hd⟩
    use d
    obtain ⟨x, hx⟩ := h
    use x
    constructor
    · exact hx
    · intro p hp
      rw [mem_ball]
      exact hd p hp x hx
  · rintro ⟨d, c, hc, hs⟩
    use 2 * d
    intro x hx y hy
    have hxb : x ∈ ball c d := hs hx
    have hyb : y ∈ ball c d := hs hy
    rw [mem_ball'] at hyb
    rw [mem_ball] at hxb
    have := Topology.dist_triangle x y c
    linarith [hxb, hyb, this]

end test
