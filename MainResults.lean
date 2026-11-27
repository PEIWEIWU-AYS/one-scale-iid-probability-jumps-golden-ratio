import OneScaleRungRoots
import OneScaleClassification
import WeightedSharp
import WeightedBridge
import OneScaleTailReductionRanks
import ScaleLift
import OneScaleTailReduction
import OneScaleNonattainment
import OneScaleGolden
import OneScaleLaw
import OneScaleLocations
import FiniteEndpoint

open IidJumpSpectra Set Filter
open scoped Topology

namespace OneScale

/-- The jump assertion for the exact Borel formulation with support in
[a,1] and c*a>1, in every left neighborhood of the golden ratio. -/
theorem original_one_scale_infinite {a : ℝ} (ha : a < golden) :
    {b : ℝ | max a 1 < b ∧ b < golden ∧ ∃ J : ℝ, 0 < J ∧
      RightJump (fun c => sSup (OriginalLawValues c)) b J}.Infinite := by
  have h := infinitely_many_oneScale_jumps (max_lt ha one_lt_golden)
  apply h.mono
  rintro b ⟨hb,hφ,J,hJ,hg⟩
  have h1 := (le_max_right a 1).trans_lt hb
  refine ⟨hb,hφ,J,hJ,fun t hbt => ?_⟩
  change sSup (OriginalLawValues b) + J ≤ sSup (OriginalLawValues t)
  rw [← beta_eq_original h1, ← beta_eq_original (h1.trans hbt)]
  exact hg t hbt

/-- On the original Borel domain, an infinite subset of the two explicit
ladder families give positive jumps in every left neighborhood of φ. -/
theorem original_ladder_jumps {a : ℝ} (ha : a < golden) :
    {b : ℝ | max a 1 < b ∧ b < golden ∧ LadderCandidate b ∧ ∃ J : ℝ, 0 < J ∧
      RightJump (fun c => sSup (OriginalLawValues c)) b J}.Infinite := by
  apply (infinitely_many_ladder_jumps (max_lt ha one_lt_golden)).mono
  rintro b ⟨hb,hφ,hL,J,hJ,hg⟩
  have h1 := (le_max_right a 1).trans_lt hb
  refine ⟨hb,hφ,hL,J,hJ,fun t hbt => ?_⟩
  change sSup (OriginalLawValues b) + J ≤ sSup (OriginalLawValues t)
  rw [← beta_eq_original h1, ← beta_eq_original (h1.trans hbt)]
  exact hg t hbt

#print axioms rung_root_existsUnique
#print axioms rungRoot_strictMono
#print axioms rungRoot_tendsto_golden
#print axioms original_jump_iff_ladder
#print axioms rankMaximum_strict
#print axioms rank_jump_iff
#print axioms WeightedSharp.coefficients_necessary
#print axioms WeightedBridge.iidWin_le_beta_add_spread
#print axioms beta_integer_ranks
#print axioms beta_fixed_canonical_menu
#print axioms canonical_edge_iff
#print axioms original_golden_nonattainment
#print axioms golden_gap_on_fixed_support
#print axioms unrestricted_golden_lower
#print axioms original_golden_value
#print axioms original_tendsto_golden
#print axioms original_golden_jump
#print axioms jump_location
#print axioms original_ladder_jumps
#print axioms original_one_scale_infinite
#print axioms IidInfiniteJumps.inverse_log_bounds
#print axioms IidInfiniteJumps.infinitely_many_values
#print axioms IidStaircase.many_finite_jumps_before_two

end OneScale
