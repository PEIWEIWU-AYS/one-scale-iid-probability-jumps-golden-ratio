import EndpointAsymptotics.SplitRankClusters
import EndpointAsymptotics.OptimalCubeMass
import EndpointAsymptotics.RankCeilingCost
import EndpointAsymptotics.UniversalLabelCeiling

open Finset OneScale ClosedSpectrum EndpointRecursion IidJumpSpectra Filter
open scoped Topology BigOperators
noncomputable section
namespace FullRankWindow

theorem threshold_near_two {n : ℕ} {c : ℝ} (hc : 1<c)
    (root : (2-c)*c^(n+5)=1) : 15/8<c := by
  have mono := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤15/8) (show 5≤n+5 by omega)
  have big : 1 < (2-15/8:ℝ)*(15/8)^(n+5) := by norm_num at mono ⊢; linarith only [mono]
  by_contra! le
  rcases le.eq_or_lt with eq | lt
  · rw [eq] at root; linarith
  · have small := threshold_opens_right (n:=n+4) hc lt root
    linarith only [big,small]

theorem threshold_diagonal_gain {n : ℕ} {c : ℝ} (hc : 1<c) (hc2 : c<2)
    (root : (2-c)*c^(n+5)=1) :
    peak n + (3/64)*Real.log ((n:ℝ)+2)*(x n)^2 ≤ extremal 2 c := by
  obtain ⟨w,hw,hs,hm⟩ := optimal_cube_mass n
  have split := split_rank_lower (threshold_near_two hc root) hc2 root w hw
  rw [hs] at split
  have logb := log_le_sum_deficit (n+1)
  push_cast at logb
  rw [show (n:ℝ)+1+1=n+2 by ring] at logb
  nlinarith only [mul_le_mul_of_nonneg_right logb (sq_nonneg (x n)),hm,split]

/-- At a multinacci root with m=n+5, an improving weak block must have
more than m-7+(9/64)log(m-3) labels, uniformly over weights and odds. -/
theorem threshold_witness_log_excess :
    ∀ᶠ n : ℕ in atTop, ∀ (c : ℝ), 1<c → c<2 → (2-c)*c^(n+5)=1 →
      ∀ (l : ℕ) (r : ℝ), 0≤r → ∀ (y w : Fin l → ℝ), (∀ i, 0<y i) → Mass w →
      extremal 2 c < blockValue (1/(1+r)) (closedScore c y w) (closedPairs c y w) →
      (n:ℝ)-2+(9/64)*Real.log ((n:ℝ)+2)<l := by
  obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp 22)
  filter_upwards [rank_ceiling_cost_uniform,eventually_ge_atTop N] with n cost beyond
  intro c hc hc2 root l r hr y w hy hw win
  have hl : 0<l := by
    cases l with
    | zero => simpa using hw.2
    | succ k => omega
  let k := l-(n+1)
  have ub := weak_le_ceiling_of_card_le hl (show l≤(n+k)+1 by dsimp [k];omega) hc2 hr y w hy hw
  have lt := (threshold_diagonal_gain hc hc2 root).trans_lt (win.trans_le (ub.trans (cost k r hr)))
  have hs : 0 < (x n)^2 := pow_pos (xpos n) _
  have cmp : (3/64)*Real.log ((n:ℝ)+2)<1+(k:ℝ)/3 :=
    (mul_lt_mul_right hs).mp (lt_of_add_lt_add_left lt)
  have ne : n+1≤l := by
    by_contra! small
    have kz : k=0 := by dsimp [k];omega
    rw [kz,Nat.cast_zero] at cmp
    have nt : (N:ℝ)≤n := by exact_mod_cast beyond
    have logb : 22 < Real.log ((n:ℝ)+2) := by
      rw [←Real.log_exp 22]
      exact Real.log_lt_log (Real.exp_pos _) (by linarith only [hN,nt])
    linarith
  have eq : (k:ℝ)=(l:ℝ)-(n+1) := by simp [k,Nat.cast_sub ne]
  linarith only [eq,cmp]

/-- Any fixed additional number of ranks, with arbitrary mixing odds, is
eventually exceeded by the unrestricted probability at the threshold itself. -/
theorem threshold_beats_fixed_ceilings (extra : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (c : ℝ), 1<c → c<2 → (2-c)*c^(n+5)=1 →
      ∃ gap : ℝ, 0<gap ∧ ∀ r : ℝ, 0≤r →
      (peak (n+4+extra)+2*r+r^2)/(1+3*r+3*r^2)+gap ≤ extremal 2 c := by
  obtain ⟨C,co⟩ := rank_ceiling_cost (4+extra)
  filter_upwards [co,sum_deficit_atTop.eventually_gt_atTop (64*(C+1))] with n cost large
  intro c hc hc2 root
  obtain ⟨w,hw,hs,hm⟩ := optimal_cube_mass n
  have pop := split_rank_lower (threshold_near_two hc root) hc2 root w hw
  rw [hs] at pop
  have hpos : 0<(x n)^2 := pow_pos (xpos n) _
  have nonneg : 0≤∑ j ∈ range (n+1), x j := sum_nonneg (fun j _ => (xpos j).le)
  refine ⟨(x n)^2,hpos,fun r hr => ?_⟩
  have cap := cost r hr
  rw [←Nat.add_assoc] at cap
  nlinarith only [cap, hm, pop, mul_lt_mul_of_pos_right large hpos,
    mul_nonneg nonneg hpos.le]

#print axioms threshold_diagonal_gain
#print axioms threshold_witness_log_excess
#print axioms threshold_beats_fixed_ceilings
end FullRankWindow
