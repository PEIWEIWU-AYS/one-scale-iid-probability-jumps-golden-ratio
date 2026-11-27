import LowerLadder
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open IidJumpSpectra Filter
open scoped Topology

namespace IidInfiniteJumps

noncomputable def logDepth (c : ℝ) := -Real.log (2-c) / Real.log c

theorem logDepth_pos {c : ℝ} (hc : 1 < c) (hc' : c < 2) : 0 < logDepth c := by
  dsimp [logDepth]
  apply div_pos (neg_pos.mpr _) (Real.log_pos hc)
  exact Real.log_neg (by linarith) (by linarith)

/-- At an exact integer depth, use that depth for the upper bound and one
less atom transition for the strict lower construction. -/
theorem depth_window {c : ℝ} (hc : 1 < c) (hc' : c < 2) :
    ∃ n : ℕ, n < logDepth c ∧ logDepth c ≤ n+1 ∧
      (c⁻¹)^(n+1) ≤ 2-c ∧ 2-c < (c⁻¹)^n := by
  have hpos := logDepth_pos hc hc'
  have hceil : 0 < ⌈logDepth c⌉₊ := Nat.ceil_pos.mpr hpos
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hceil.ne'
  have h₁ : (n:ℝ) < logDepth c := Nat.lt_ceil.mp (by omega)
  have h₂ := Nat.le_ceil (logDepth c)
  rw [hn, Nat.cast_succ] at h₂
  refine ⟨n,h₁,h₂,?_,?_⟩
  · apply (Real.log_le_log_iff (by positivity) (by linarith)).mp
    rw [Real.log_pow, Real.log_inv, Nat.cast_succ]
    have h := (div_le_iff₀ (Real.log_pos hc)).mp h₂
    linarith
  · apply (Real.log_lt_log_iff (by linarith) (by positivity)).mp
    rw [Real.log_pow, Real.log_inv]
    have h := (lt_div_iff₀ (Real.log_pos hc)).mp h₁
    linarith

end IidInfiniteJumps
