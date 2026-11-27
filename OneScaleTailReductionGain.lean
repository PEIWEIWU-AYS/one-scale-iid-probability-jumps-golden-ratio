import OneScaleJumpSize
import OneScaleTailReductionPath

namespace OneScale

/-- Every new rank above the first four strictly increases the optimum. -/
theorem rankMaximum_tail_strict {N : ℕ} (hN : 4≤N) : rankMaximum N < rankMaximum (N+1) := by
  let n := N-3
  have hn : 0<n := by dsimp [n]; omega
  have he : n+3=N := by dsimp [n]; omega
  have first := rankMaximum_attained (N := n+3) (by omega)
  have next := rankMaximum_attained (N := (n+1)+3) (by omega)
  rw [rank_path_values] at first next
  have gain := Tail.path_step_strict hn first next
  simpa [he,show n+1+3=N+1 by omega] using gain

#print axioms rankMaximum_tail_strict

end OneScale
