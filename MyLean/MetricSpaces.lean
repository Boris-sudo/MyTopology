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

theorem dist_nonneg {α} {x y : α} (dist : α → α → ℝ)
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

@[simp] theorem dist_self (x : α) : dist x x = 0 :=
  PseudoMetric.dist_self x

@[simp] theorem dist_comm (x y : α) : dist x y = dist y x :=
  PseudoMetric.dist_comm x y

@[simp] theorem dist_triangle (x y z : α) : dist x y ≤ dist x z + dist z y :=
  PseudoMetric.dist_triangle x y z

@[simp] theorem dist_triangle_left (x y z : α) : dist x y ≤ dist z x + dist z y := by
  rw [dist_comm z]; apply dist_triangle

@[simp] theorem dist_triangle_right (x y z : α) : dist x y ≤ dist x z + dist y z := by
  rw [dist_comm y]; apply dist_triangle

class Metric (α : Type) extends PseudoMetric α where
  dist_eq : ∀ x y : α, dist x y = 0 → x = y

variable {α : Type} [Metric α]

@[simp] theorem dist_eq_iff (x y : α) : dist x y = 0 → x = y :=
  Metric.dist_eq x y

end Topology
