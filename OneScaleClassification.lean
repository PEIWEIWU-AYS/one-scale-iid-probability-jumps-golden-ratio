import OneScaleEarlyRanks
import OneScaleTailReductionGain
import OneScaleLaw

open IidJumpSpectra Set
namespace OneScale

/-- The coefficient-free cubic increases whenever a new rank becomes available. -/
theorem rankMaximum_strict {N : ℕ} (hn : 0<N) :
    rankMaximum N < rankMaximum (N+1) := by
  by_cases h : N≤3
  · exact early_rank_strict hn h
  · exact rankMaximum_tail_strict (by omega)

/-- Every ordinary or branching threshold is a genuine jump of the original
strict Borel one-scale optimization, and every subcritical jump is such a threshold. -/
theorem original_jump_iff_ladder {c : ℝ} (hc : 1<c) (hg : c<golden) :
    (∃ J : ℝ, 0<J ∧ RightJump (fun s => sSup (OriginalLawValues s)) c J) ↔ LadderCandidate c := by
  have transfer (J : ℝ) :
      RightJump (fun s => sSup (OriginalLawValues s)) c J ↔ RightJump beta c J := by
    constructor <;> intro h s hs
    · have a := h s hs
      change sSup (OriginalLawValues c)+J ≤ sSup (OriginalLawValues s) at a
      rwa [← beta_eq_original hc,← beta_eq_original (hc.trans hs)] at a
    · change sSup (OriginalLawValues c)+J ≤ sSup (OriginalLawValues s)
      rw [← beta_eq_original hc,← beta_eq_original (hc.trans hs)]
      exact h s hs
  constructor
  · rintro ⟨J,hJ,h⟩
    exact jump_location hc hg hJ ((transfer J).1 h)
  · intro cand
    have can : CanonicalLevel c c := by simpa only [CanonicalLevel,LadderCandidate,eq_comm] using cand
    obtain ⟨n,he⟩ := (canonical_iff_rung c c).1 can
    have hn : 0<n := by
      by_contra! h
      obtain rfl : n=0 := by omega
      change c=1 at he
      linarith
    let J := rankMaximum (n+1)-rankMaximum n
    exact ⟨J,sub_pos.mpr (rankMaximum_strict hn),
      (transfer J).2 ((rank_jump_iff hc hg he.symm).2 le_rfl)⟩

#print axioms original_jump_iff_ladder
end OneScale
