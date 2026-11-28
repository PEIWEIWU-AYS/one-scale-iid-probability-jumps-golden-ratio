import EndpointAsymptotics.FullRankTransfer
import EndpointAsymptotics.RankInterior

open Finset OneScale ClosedSpectrum
open scoped BigOperators
noncomputable section
namespace FullRankWindow

/-- This ceiling applies at every coefficient below two, even where the
full rank pattern cannot itself be realized. The labels and odds may be
chosen arbitrarily below the given size bound. -/
theorem weak_le_ceiling_of_card_le {l M : ℕ} {c r : ℝ}
    (hl : 0<l) (hM : l≤M+1) (hc : c<2) (hr : 0≤r)
    (x w : Fin l → ℝ) (hx : ∀ i, 0<x i) (hw : Mass w) :
    blockValue (1/(1+r)) (closedScore c x w) (closedPairs c x w) ≤
      (peak M+2*r+r^2)/(1+3*r+3*r^2) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  have bound := (closedScore_le_peak hc x w hx hw).trans
    ((strictMono_nat_of_lt_succ peak_increases).monotone (by omega : k≤M))
  have pair : closedPairs c x w≤1 := by
    unfold closedPairs
    calc
      _ ≤ ∑ i, ∑ j, w i*w j := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hw.1 _) (hw.1 _)
      _ = 1 := by simp only [←mul_sum,hw.2,mul_one]
  rw [blockValue_odds _ _ hr]
  have pair_bound := mul_le_mul_of_nonneg_left pair (show 0≤2*r by positivity)
  exact div_le_div_of_nonneg_right (by linarith only [bound,pair_bound]) (by positivity)

#print axioms weak_le_ceiling_of_card_le
end FullRankWindow
