import EndpointAsymptotics.FullRankWeights
import Mathlib.Order.Fin.Basic

open Finset OneScale
open scoped BigOperators
noncomputable section
namespace FullRankWindow

theorem peak_increases (n : ℕ) : peak n < peak (n+1) := by
  let s := Real.sqrt (3*(1-peak n))
  have h := peak_lt (n:=n)
  have hs : s^2=3*(1-peak n) := Real.sq_sqrt (by linarith)
  have hs0 : 0≤s := Real.sqrt_nonneg _
  have hs1 : 1<s := by
    by_contra! hh
    have bad := pow_le_pow_left₀ hs0 hh 2
    rw [hs,one_pow] at bad
    linarith
  change peak n < 2/(3*s)
  apply (lt_div_iff₀ (by positivity)).2
  have pos : 0<(s-1)^2*(s+2) := mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  nlinarith only [pos,congrArg (fun z : ℝ => s*z) hs]

theorem delete_zero {m : ℕ} (w : Fin (m+1) → ℝ) (i : Fin (m+1)) (hi : w i=0) :
    rankScore w=rankScore (w ∘ i.succAbove) := by
  classical
  simp only [rankScore, Fin.sum_univ_succAbove _ i,hi,zero_mul,mul_zero,
    ite_self,sum_const_zero,add_zero,zero_add,Fin.succAbove_lt_succAbove_iff,Function.comp_apply]

/-- An exact maximizing probability vector cannot have zero mass at a label. -/
theorem optimal_weights_positive {n : ℕ} (w : Fin (n+1) → ℝ)
    (hw : Mass w) (hopt : rankScore w=peak n) : ∀ i,0<w i := by
  intro i
  by_contra! h
  have hi := le_antisymm h (hw.1 i)
  cases n with
  | zero =>
    have tot := hw.2
    have he : i=0 := Fin.ext (by omega)
    subst i
    simp [hi] at tot
  | succ m =>
    have reduced : Mass (w ∘ i.succAbove) := by
      refine ⟨fun j => hw.1 _,?_⟩
      have tot := hw.2
      simpa only [Fin.sum_univ_succAbove _ i,hi,zero_add,Function.comp_apply] using tot
    have sub := (rank_peak m).2 _ reduced
    rw [←delete_zero w i hi,hopt] at sub
    exact (not_le_of_gt (peak_increases m)) sub

#print axioms optimal_weights_positive
end FullRankWindow
