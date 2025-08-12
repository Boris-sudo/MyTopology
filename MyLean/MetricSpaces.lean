import Mathlib.Data.Real.Basic
import Mathlib.Tactic


namespace Topology

variable {α : Type} {s₁ t₁ s₂ t₂ : Set α}

/-
  ### MetricSpaces
-/

class Dist (α : Type) where
  dist : α → α → ℝ

export Dist (dist)

theorem dist_nonneg' {α} {x y : α} (dist : α → α → ℝ)
  (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
  (dist_triangle : ∀ x y z : α, dist x y ≤ dist x z + dist z y) : 0 ≤ dist x y :=
  have : 0 ≤ 2 * dist x y := calc
    0 = dist x x := (dist_self _).symm
    _ ≤ dist x y + dist y x := dist_triangle _ _ _
    _ = 2 * dist x y := by rw [two_mul, dist_comm]
  nonneg_of_mul_nonneg_right this two_pos

class PseudoMetric (α : Type) extends Dist α where
  dist_self : ∀ x : α, dist x x = 0
  dist_comm : ∀ x y : α, dist x y = dist y x
  dist_triangle : ∀ x y z : α, dist x y ≤ dist x z + dist z y

variable [PseudoMetric α]

@[simp]
theorem dist_self (x : α) : dist x x = 0 :=
  PseudoMetric.dist_self x

@[simp]
theorem dist_comm (x y : α) : dist x y = dist y x :=
  PseudoMetric.dist_comm x y

@[simp]
theorem dist_triangle (x y z : α) : dist x y ≤ dist x z + dist z y :=
  PseudoMetric.dist_triangle x y z

@[simp]
theorem dist_triangle_left (x y z : α) : dist x y ≤ dist z x + dist z y := by
  rw [dist_comm z]; apply dist_triangle

@[simp]
theorem dist_triangle_right (x y z : α) : dist x y ≤ dist x z + dist y z := by
  rw [dist_comm y]; apply dist_triangle

class Metric (α : Type) extends PseudoMetric α where
  dist_eq : ∀ x y : α, dist x y = 0 → x = y

variable {α : Type} [Metric α]

@[simp] theorem dist_eq_iff (x y : α) : dist x y = 0 → x = y :=
  Metric.dist_eq x y

theorem dist_no_eq (x y : α) : dist x y ≠ 0 ↔ x ≠ y := by
  constructor
  · intro h
    rw [ne_eq] at h ⊢
    intro a
    subst a
    simp only [dist_self, not_true_eq_false] at h
  · intro h
    rw [ne_eq] at h ⊢
    intro ha
    apply dist_eq_iff at ha
    contradiction

@[simp, bound]
theorem dist_nonneg {x y : α} : 0 ≤ dist x y :=
  dist_nonneg' dist dist_self dist_comm dist_triangle

/-
  ### Balls
-/
variable {x y z : α} {δ ε ε₁ ε₂ : ℝ} {s : Set α}

def ball (x : α) (ε : ℝ) : Set α := { y | dist y x < ε }

@[simp]
theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε :=
  Iff.rfl

theorem mem_ball' : y ∈ ball x ε ↔ dist x y < ε := by
  rw [ball]; simp

theorem ball_exist (hy : y ∈ ball x ε) : 0 < ε :=
  lt_of_le_of_lt dist_nonneg hy

theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε := by
  rwa [mem_ball, dist_self]

@[simp]
theorem nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε := by
  constructor
  · intro ⟨y, h⟩
    exact ball_exist h
  · intro h
    exact ⟨x, mem_ball_self h⟩

@[simp]
theorem ball_eq_empty : ball x ε = ∅ ↔ ε ≤ 0 := by
  rw [← Set.not_nonempty_iff_eq_empty, nonempty_ball, not_lt]

@[simp]
theorem ball_zero : ball x 0 = ∅ := by
  rw [ball_eq_empty]

/- If point `p` belongs to a `ball x ε`, then exist `ε' < ε` such that `p ∈ ball x ε'`.
-/
theorem exist_lt_mem_ball_of_mem_ball (h : y ∈ ball x ε) : ∃ ε' < ε, y ∈ ball x ε' := by
  simp only [mem_ball] at h ⊢
  exact ⟨(dist y x + ε) / 2, by linarith, by linarith⟩

def closedBall (x : α) (ε : ℝ) : Set α := {y | dist x y ≤ ε}

@[simp]
theorem mem_closedBall : y ∈ closedBall x ε ↔ dist x y ≤ ε :=
  Iff.rfl

theorem mem_closedBall' : y ∈ closedBall x ε ↔ dist y x ≤ ε := by
  rw [closedBall]; simp

theorem mem_closedBall_self (h : 0 ≤ ε) : x ∈ closedBall x ε := by
  rw [closedBall]; simp [h]

def sphere (x : α) (ε : ℝ) : Set α := {y | dist x y = ε}

@[simp]
theorem mem_sphere : y ∈ sphere x ε ↔ dist x y = ε :=
  Iff.rfl

theorem mem_sphere' : y ∈ sphere x ε ↔ dist y x = ε := by
  rw [sphere]; simp

theorem ne_of_mem_sphere (h : y ∈ sphere x ε) (hε : ε ≠ 0) : x ≠ y := by
  apply (dist_no_eq x y).1
  simp at h
  simp_all only [ne_eq, not_false_eq_true]

theorem sphere_eq_closedBall_sub_ball : sphere x ε = (closedBall x ε) \ (ball x ε) := by
  ext a
  constructor
  · intro ha
    simp only [mem_sphere] at ha
    simp only [closedBall, ball]
    apply And.intro <;> simp <;> linarith
  · intro ⟨h₁, h₂⟩
    simp only [mem_closedBall, mem_ball', mem_sphere] at h₁ h₂ ⊢
    exact le_antisymm h₁ (not_lt.mp h₂)

end Topology
