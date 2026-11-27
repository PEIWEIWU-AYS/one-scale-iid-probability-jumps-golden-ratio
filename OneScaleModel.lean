import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

open Finset Set
open scoped BigOperators

namespace OneScale

def Cfg {α : Type*} (c : ℝ) (x : α → ℝ) : Prop :=
  ∀ i, 1 ≤ x i ∧ x i < c

def Win {α : Type*} (c : ℝ) (x : α → ℝ) (i j k : α) : Prop :=
  x i + x j < c * x k

noncomputable def score {α : Type*} [Fintype α] (c : ℝ) (x w : α → ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, ∑ k, if Win c x i j k then w i * w j * w k else 0

def Mass {α : Type*} [Fintype α] (w : α → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1

def values (c : ℝ) : Set ℝ :=
  {b | ∃ (n : ℕ) (x w : Fin n → ℝ), Cfg c x ∧ Mass w ∧ score c x w = b}

noncomputable def beta (c : ℝ) : ℝ := sSup (values c)

end OneScale
