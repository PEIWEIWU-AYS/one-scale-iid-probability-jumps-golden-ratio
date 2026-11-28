import EndpointAsymptotics.FullRankTransfer
import EndpointAsymptotics.WeightedRecursion
import Height

open IidJumpSpectra IidInfiniteJumps Filter Set
open scoped Topology
noncomputable section
namespace FullRankWindow

theorem optimal_deficit (n : ℕ) : 2/3-peak n=EndpointRecursion.x n/3 := by
  induction n with
  | zero => norm_num [peak,EndpointRecursion.x]
  | succ n ih =>
    let a := EndpointRecursion.x n
    let s := Real.sqrt (1+a)
    have ha : 0<a := EndpointRecursion.xpos n
    have id : 3*(1-peak n)=1+a := by change 3*(1-peak n)=1+EndpointRecursion.x n; linarith only [ih]
    have hs : 0<s := Real.sqrt_pos.mpr (by linarith)
    have hs2 : s^2=1+a := Real.sq_sqrt (by linarith)
    change 2/3-2/(3*Real.sqrt (3*(1-peak n))) = (2*a/(s*(1+s)))/3
    rw [id]
    change 2/3-2/(3*s) = (2*a/(s*(1+s)))/3
    field_simp [hs.ne',show 1+s≠0 by linarith]
    linear_combination 18*s*hs2

private theorem weighted_shift_limit :
    Tendsto (fun n : ℕ => ((n:ℝ)+2)*(2/3-peak n)) atTop (𝓝 (4/9)) := by
  have rat := (tendsto_const_nhds (x := (1:ℝ))).add (tendsto_const_div_atTop_nhds_zero_nat 2)
  have mix : Tendsto (fun n : ℕ => (1+2/(n:ℝ))*((n:ℝ)*(EndpointRecursion.x n/3)))
      atTop (𝓝 (4/9)) := by
    simpa using rat.mul EndpointRecursion.weighted_deficit_limit
  apply mix.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [optimal_deficit]
  have hn' : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  field_simp
  ring

/-- For all large logarithmic depths, the genuine population deficit times
that depth is bounded above by any number strictly greater than 4/9. -/
theorem population_large_depth {v : ℝ} (hv : 4/9<v) :
    ∃ K : ℕ, ∀ c : ℝ, 1<c → c<2 → (K:ℝ)≤logDepth c →
      logDepth c*(2/3-extremal 2 c)<v := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp (weighted_shift_limit.eventually_lt_const hv)
  refine ⟨K+2,?_⟩
  intro c hc h2 hdeep
  obtain ⟨n,_,hhi,_,hgeom⟩ := depth_window hc h2
  push_cast at hdeep hhi
  have hk : K+1≤n := by
    exact_mod_cast (show (K:ℝ)+1≤(n:ℝ) by linarith only [hdeep,hhi])
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
  have hc0 : 0<c := by linarith
  have win : (2-c)*c^(m+1)≤1 := by
    apply (le_div_iff₀ (pow_pos hc0 (m+1))).1
    simpa only [one_div,inv_pow] using hgeom.le
  have pop := peak_le_population hc h2 win
  have hL := logDepth_pos hc h2
  have hp := peak_lt (n:=m)
  have him : logDepth c≤(m:ℝ)+2 := by push_cast at hhi; linarith
  calc
    _ ≤ logDepth c*(2/3-peak m) := mul_le_mul_of_nonneg_left (by linarith only [pop]) hL.le
    _ ≤ ((m:ℝ)+2)*(2/3-peak m) := mul_le_mul_of_nonneg_right him (sub_nonneg.mpr hp.le)
    _ < v := hK m (by omega)

/-- In particular the bound is uniform on a left neighborhood of the endpoint.
This is the upper half of the proposed endpoint asymptotic. -/
theorem population_endpoint_four_ninths {v : ℝ} (hv : 4/9<v) :
    ∀ᶠ c in 𝓝[<] (2:ℝ), logDepth c*(2/3-extremal 2 c)<v := by
  obtain ⟨K,hK⟩ := population_large_depth hv
  let d := 2-(1/2:ℝ)^K
  have hd : d<2 := by dsimp [d]; linarith [show 0<(1/2:ℝ)^K by positivity]
  have left : ∀ᶠ c in 𝓝[<] (2:ℝ), c<2 := self_mem_nhdsWithin
  have right : ∀ᶠ c in 𝓝[<] (2:ℝ), d<c := (eventually_gt_nhds hd).filter_mono nhdsWithin_le_nhds
  have one : ∀ᶠ c in 𝓝[<] (2:ℝ), 1<c :=
    (eventually_gt_nhds (by norm_num : (1:ℝ)<2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [left,right,one] with c h2 hdc hc
  apply hK c hc h2
  have hi : (1/2:ℝ)≤c⁻¹ := by
    rw [←one_div c]
    exact one_div_le_one_div_of_le (by linarith) h2.le
  have less : 2-c<c⁻¹^K := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hi K
    dsimp only [d] at hdc
    linarith only [hdc,h]
  have logs := Real.log_lt_log (by linarith : 0<2-c) less
  rw [Real.log_pow,Real.log_inv] at logs
  unfold logDepth
  apply (le_div_iff₀ (Real.log_pos hc)).2
  nlinarith only [logs]

#print axioms population_endpoint_four_ninths
end FullRankWindow
