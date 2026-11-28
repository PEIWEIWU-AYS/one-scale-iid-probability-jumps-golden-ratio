import EndpointAsymptotics.MultinacciPopulationCap
import EndpointAsymptotics.RankModelSequence
import EndpointAsymptotics.RankPopulationEndpoint

open MultinacciBands IidJumpSpectra IidInfiniteJumps FullRankWindow Filter Set
open scoped Topology
noncomputable section
namespace MultinacciBands

private theorem delay_ratio_zero : Tendsto (fun n : ℕ => delayBudget n/n) atTop (𝓝 0) := by
  have logn : Tendsto (fun n : ℕ => Real.log (n:ℝ)/n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have sum := (((tendsto_const_div_atTop_nhds_zero_nat (Real.log 4)).add logn).div_const
      (Real.log (3/2))).add (tendsto_const_div_atTop_nhds_zero_nat 1)
  have res : Tendsto (fun n : ℕ => (Real.log 4/n+Real.log (n:ℝ)/n)/Real.log (3/2)+1/n)
      atTop (𝓝 0) := by simpa using sum
  apply res.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have np : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  rw [delayBudget,Real.log_mul (by norm_num) np]
  ring

private def capFactor (n : ℕ) : ℝ :=
  (1-1/(n:ℝ))*4/(9*(Real.sqrt (1+2/(n:ℝ))+4*Real.sqrt (delayBudget n/n))^2)

private theorem factor_limit : Tendsto capFactor atTop (𝓝 (4/9)) := by
  have a := ((tendsto_const_nhds (x:=(1:ℝ))).add (tendsto_const_div_atTop_nhds_zero_nat 2)).sqrt
  have b := (delay_ratio_zero.sqrt).const_mul 4
  have d := ((a.add b).pow 2).const_mul 9
  have u := ((tendsto_const_nhds (x:=(1:ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat 1)).mul_const 4
  convert u.div d (by norm_num) using 1
  norm_num

private theorem factor_value {n : ℕ} (hn : 0<n) :
    capFactor n = ((n:ℝ)-1)*4/(9*(Real.sqrt ((n:ℝ)+2)+4*Real.sqrt (delayBudget n))^2) := by
  have h : 0<(n:ℝ) := by exact_mod_cast hn
  let t := Real.sqrt (n:ℝ)
  have ht : 0<t := Real.sqrt_pos.mpr h
  have ht2 : t^2=n := Real.sq_sqrt h.le
  have a : Real.sqrt (1+2/(n:ℝ))=Real.sqrt ((n:ℝ)+2)/t := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  have bd : 0≤delayBudget n := by
    have np : 1≤(n:ℝ) := by exact_mod_cast hn
    dsimp [delayBudget]
    have pos := Real.log_nonneg (show (1:ℝ)≤4*n by linarith)
    positivity
  have b : Real.sqrt (delayBudget n/n)=Real.sqrt (delayBudget n)/t := Real.sqrt_div bd _
  unfold capFactor
  rw [a,b,show Real.sqrt ((n:ℝ)+2)/t+4*(Real.sqrt (delayBudget n)/t)=
      (Real.sqrt ((n:ℝ)+2)+4*Real.sqrt (delayBudget n))/t by ring,div_pow]
  rw [ht2]
  have D : 0 < Real.sqrt ((n:ℝ)+2)+4*Real.sqrt (delayBudget n) := by positivity
  field_simp [(ne_of_gt h),D.ne']

/-- The logarithmic depth tends to infinity along all approaches from below. -/
theorem logDepth_tends_to_infinity : Tendsto logDepth (𝓝[<] (2:ℝ)) atTop := by
  apply tendsto_atTop.2
  intro a
  obtain ⟨K,hK⟩ := exists_nat_gt a
  let d := 2-(1/2:ℝ)^K
  have hd : d<2 := by dsimp only [d];linarith only [pow_pos (by norm_num : (0:ℝ)<1/2) K]
  have high : ∀ᶠ c in 𝓝[<] (2:ℝ), d<c := (eventually_gt_nhds hd).filter_mono nhdsWithin_le_nhds
  have one : ∀ᶠ c in 𝓝[<] (2:ℝ), 1<c :=
    (eventually_gt_nhds (by norm_num : (1:ℝ)<2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [high,one,self_mem_nhdsWithin] with c hdc hc h2
  change c<2 at h2
  have hi : (1/2:ℝ)≤c⁻¹ := by rw [←one_div c];exact one_div_le_one_div_of_le (by linarith) h2.le
  have small : 2-c<c⁻¹^K := by
    apply lt_of_lt_of_le _ (pow_le_pow_left₀ (by norm_num) hi K)
    dsimp only [d] at hdc;linarith
  have log := Real.log_lt_log (by linarith : 0<2-c) small
  rw [Real.log_pow,Real.log_inv] at log
  apply hK.le.trans
  unfold logDepth
  apply (le_div_iff₀ (Real.log_pos hc)).2
  linarith only [log]

private theorem cap_at_depth {c : ℝ} (hc : 1<c) (hc2 : c<2)
    {m : ℕ} (hm : 32≤m) (upper : logDepth c≤(m:ℝ)) (lower : (m:ℝ)-1≤logDepth c) :
    capFactor m ≤ logDepth c*(2/3-extremal 2 c) := by
  obtain ⟨u,_,_,root⟩ := jumps_along_finite_models
  let k := m-2
  have mk : k+2=m := by dsimp [k];omega
  obtain ⟨u1,u2,eq,_⟩ := root k
  rw [mk] at eq
  have le : c≤u k := by
    by_contra! gt
    have eq' : (2-u k)* (u k)^((k+1)+1)=1 := by simpa only [←mk] using eq
    have fail := threshold_opens_right u1 gt eq'
    change (2-c)*c^(k+2)<1 at fail
    rw [mk] at fail
    have posc := zero_lt_one.trans hc
    have lg := Real.log_lt_log (mul_pos (sub_pos.mpr hc2) (pow_pos posc m)) fail
    rw [Real.log_one,Real.log_mul (sub_pos.mpr hc2).ne' (pow_pos posc m).ne',Real.log_pow] at lg
    have b := (div_le_iff₀ (Real.log_pos hc)).mp upper
    linarith only [lg,b]
  let g := 4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m))^2)
  have g0 : 0≤g := by dsimp [g];positivity
  have defc : g ≤ 2/3-extremal 2 c := by
    have bound := unrestricted_upper hm u1 u2 eq
    have mono := extremal_mono 2 le
    dsimp only [g];linarith only [bound,mono]
  rw [factor_value (by omega : 0<m)]
  calc
    _ = ((m:ℝ)-1)*g := by dsimp only [g];ring
    _ ≤ logDepth c*g := mul_le_mul_of_nonneg_right lower g0
    _ ≤ _ := mul_le_mul_of_nonneg_left defc (logDepth_pos hc hc2).le

/-- The exact leading asymptotic for the original, unrestricted population
function as the real parameter approaches two from below. -/
theorem population_endpoint_limit : Tendsto (fun c => logDepth c*(2/3-extremal 2 c))
    (𝓝[<] (2:ℝ)) (𝓝 (4/9)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have M : Tendsto (fun c => ⌈logDepth c⌉₊) (𝓝[<] (2:ℝ)) atTop :=
      tendsto_nat_ceil_atTop.comp logDepth_tends_to_infinity
    have lower := M.eventually (factor_limit.eventually_const_lt ha)
    have one : ∀ᶠ c in 𝓝[<] (2:ℝ), 1<c :=
      (eventually_gt_nhds (by norm_num : (1:ℝ)<2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [lower,M.eventually (eventually_ge_atTop 32),one,self_mem_nhdsWithin] with c lt big hc h2
    change c<2 at h2
    have bound := Nat.ceil_lt_add_one (logDepth_pos hc h2).le
    exact lt.trans_le (cap_at_depth hc h2 big (Nat.le_ceil _) (by linarith only [bound]))
  · intro a ha
    exact population_endpoint_four_ninths ha

#print axioms population_endpoint_limit
end MultinacciBands
