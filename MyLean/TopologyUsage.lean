import MyLean.Topology
import Mathlib.Data.Real.Basic

open Topology Set

namespace test

-- доказательство того, что дискретное пространоство - топология
@[simp]
instance DiscreteTopology : Topology.TopologicalSpace ℝ where
  isOpen := fun _ ↦ true
  isOpen_empty := rfl
  isOpen_univ := rfl
  isOpen_inter := by simp
  isOpen_union := by simp

-- доказательство того, что антидискретное пространство - топология
@[simp]
instance AntiDiscreteTopology : Topology.TopologicalSpace ℝ where
  isOpen x := x = ∅ ∨ x = univ
  isOpen_empty := by simp
  isOpen_univ := by simp
  isOpen_inter := by rintro _ _ (rfl | rfl) (rfl | rfl) <;> simp
  isOpen_union := by rintro _ _ (rfl | rfl) (rfl | rfl) <;> simp

lemma lemma1 : AntiDiscreteTopology < DiscreteTopology := by
  simp only [instLTTopologicalSpace]
  intro a hs
  simp only [AntiDiscreteTopology] at hs
  rcases hs with (rfl | rfl)
  · exact DiscreteTopology.isOpen_empty
  · exact DiscreteTopology.isOpen_univ

end test
