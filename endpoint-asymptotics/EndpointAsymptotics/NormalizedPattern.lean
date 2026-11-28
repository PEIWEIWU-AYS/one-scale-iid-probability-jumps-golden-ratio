import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter Set
open scoped Topology BigOperators

namespace ClosedSpectrum

/-- Normalize every positive realization to unit mass before passing to a
subsequence. The limiting weak realization retains a positive coordinate. -/
theorem normalized_pattern {α : Type*} [Fintype α] [Nonempty α]
    (H : α → α → α → Prop) (c : ℝ)
    (h : ∀ d > c, ∃ x : α → ℝ, (∀ i, 0 < x i) ∧
      ∀ i j k, H i j k → x i + x j < d * x k) :
    ∃ u : α → ℝ, (∀ i, 0 ≤ u i) ∧ (∃ i, 0 < u i) ∧
      ∀ i j k, H i j k → u i + u j ≤ c * u k := by
  classical
  let d (n : ℕ) : ℝ := c + 1 / ((n : ℝ) + 1)
  have hd (n : ℕ) : c < d n := by
    dsimp [d]
    linarith [show 0 < 1 / ((n : ℝ)+1) by positivity]
  choose x hx hw using fun n : ℕ => h (d n) (hd n)
  let D (n : ℕ) := ∑ i, x n i
  have hD (n : ℕ) : 0 < D n :=
    Finset.sum_pos (fun i _ => hx n i) Finset.univ_nonempty
  let y (n : ℕ) (i : α) := x n i / D n
  have hy (n : ℕ) : y n ∈ stdSimplex ℝ α := by
    refine ⟨fun i => div_nonneg (hx n i).le (hD n).le, ?_⟩
    dsimp only [y]
    rw [← Finset.sum_div]
    exact div_self (hD n).ne'
  obtain ⟨u,hu,φ,hφ,hlim⟩ := (isCompact_stdSimplex α).tendsto_subseq hy
  have positive : ∃ i, 0 < u i := by
    by_contra! hz
    have allzero : ∀ i, u i = 0 := fun i => le_antisymm (hz i) (hu.1 i)
    have total := hu.2
    simp [allzero] at total
  refine ⟨u,hu.1,positive,?_⟩
  intro i j k hij
  have limv (l : α) : Tendsto (fun n => y (φ n) l) atTop (𝓝 (u l)) :=
    ((continuous_apply l).tendsto u).comp hlim
  have limd : Tendsto d atTop (𝓝 c) := by
    simpa only [d,add_zero] using
      ((tendsto_const_nhds (x:=c)).add tendsto_one_div_add_atTop_nhds_zero_nat)
  apply le_of_tendsto_of_tendsto' ((limv i).add (limv j))
    ((limd.comp hφ.tendsto_atTop).mul (limv k))
  intro n
  change x (φ n) i / D (φ n) + x (φ n) j / D (φ n) ≤ d (φ n) * (x (φ n) k / D (φ n))
  rw [← add_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (hw (φ n) i j k hij).le (hD _).le

#print axioms normalized_pattern
end ClosedSpectrum
