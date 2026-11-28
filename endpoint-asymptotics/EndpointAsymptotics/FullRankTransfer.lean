import EndpointAsymptotics.FullRankWeights
import EndpointAsymptotics.ResonanceTest
import EndpointAsymptotics.ClosedSpectrum

open Finset OneScale ClosedSpectrum IidJumpSpectra
open scoped BigOperators
noncomputable section
namespace FullRankWindow

theorem closedScore_le_peak {n : ℕ} {c : ℝ} (hc : c<2) (x w : Fin (n+1) → ℝ)
    (hx : ∀ i, 0<x i) (hw : Mass w) : closedScore c x w≤peak n := by
  obtain ⟨e,he,h⟩ := sorted_dominance hc x w hx hw
  exact h.trans ((rank_peak n).2 _ he)

theorem terminal_peak_attained {n : ℕ} {c : ℝ} (hc : 1<c) (h2 : c<2)
    (h : (2-c)*c^(n+1)≤1) :
    ∃ x w : Fin (n+1) → ℝ, (∀ i,0<x i) ∧ Mass w ∧
      closedScore c x w=peak n ∧ closedPairs c x w=1 := by
  obtain ⟨x,hx,hp⟩ := sharp_rank_block hc h2 h
  obtain ⟨w,hw,wp⟩ := (rank_peak n).1
  exact ⟨x,w,hx,hw,((hp w hw).1.trans wp),(hp w hw).2⟩

/-- A quantitative population consequence for all nonnegative Borel laws:
the endpoint itself dominates the optimized m-level triple score. -/
theorem peak_le_population {n : ℕ} {c : ℝ} (hc : 1<c) (h2 : c<2)
    (h : (2-c)*c^(n+1)≤1) : peak n≤extremal 2 c := by
  obtain ⟨x,w,hx,hw,he,_⟩ := terminal_peak_attained hc h2 h
  exact he ▸ closedScore_le_extremal h2 x w hx hw

/-- The joint finite-block optimum for each prescribed odds is achieved by
the same terminal block and has this explicit value. -/
theorem fixed_odds_optimum {n : ℕ} {c r : ℝ} (hc : 1<c) (h2 : c<2)
    (h : (2-c)*c^(n+1)≤1) (hr : 0≤r) :
    IsGreatest {v : ℝ | ∃ x w : Fin (n+1) → ℝ, (∀ i,0<x i) ∧ Mass w ∧
       v=blockValue (1/(1+r)) (closedScore c x w) (closedPairs c x w)}
      ((peak n+2*r+r^2)/(1+3*r+3*r^2)) := by
  obtain ⟨x,w,hx,hw,he,hq⟩ := terminal_peak_attained hc h2 h
  refine ⟨⟨x,w,hx,hw,?_⟩,?_⟩
  · rw [blockValue_odds _ _ hr,he,hq,mul_one]
  · rintro _ ⟨z,u,hz,hu,rfl⟩
    rw [blockValue_odds _ _ hr]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have pairs : closedPairs c z u≤1 := by
      unfold closedPairs
      calc
        _ ≤ ∑ i, ∑ j, u i*u j := by
          refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
          split_ifs
          · exact le_rfl
          · exact mul_nonneg (hu.1 _) (hu.1 _)
        _ = 1 := by simp only [←mul_sum,hu.2,mul_one]
    have triple := closedScore_le_peak h2 z u hz hu
    linarith only [triple,mul_le_mul_of_nonneg_left pairs (by positivity : 0≤2*r)]

theorem optimized_block_le_population_right {n : ℕ} {c r : ℝ} (hc : 1<c) (h2 : c<2)
    (h : (2-c)*c^(n+1)≤1) (hr : 0≤r) :
    (peak n+2*r+r^2)/(1+3*r+3*r^2) ≤ rightValue c := by
  obtain ⟨x,w,hx,hw,he,hq⟩ := terminal_peak_attained hc h2 h
  have hden : 0<1+r := by linarith
  apply block_le_rightValue (zero_lt_one.trans hc)
  refine ⟨n+1,x,w,1/(1+r),hx,hw,by positivity,(div_le_one hden).2 (by linarith),?_⟩
  rw [blockValue_odds _ _ hr,he,hq,mul_one]

#print axioms fixed_odds_optimum
#print axioms peak_le_population
#print axioms optimized_block_le_population_right
end FullRankWindow
