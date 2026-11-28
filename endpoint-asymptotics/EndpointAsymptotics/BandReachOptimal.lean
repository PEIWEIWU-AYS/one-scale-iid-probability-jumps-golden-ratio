import EndpointAsymptotics.BandReach
import EndpointAsymptotics.BandReachScale
import EndpointAsymptotics.EndpointCapSlack
import EndpointAsymptotics.RankModelSequence
import Mathlib.Data.Nat.Find

noncomputable section
namespace MultinacciBands

/-- The root with index m+j is covered by a band certificate no larger
than the published cap at m. Evaluating at any later coefficient v is
allowed because the population supremum is increasing. -/
def coveredOffset (m j : ℕ) : Prop :=
  ∃ (u v r : ℝ) (K e : ℕ), 1 < u ∧ u < 2 ∧ (2-u)*u^(m+j)=1 ∧
    u ≤ v ∧ v < 2 ∧ 1 < r ∧ 0 < K ∧ 0 < e ∧ r*(1+(r⁻¹)^e) ≤ v ∧
    (r⁻¹)^(K+e) ≤ 2-v ∧
    2/3-4/(9*(Real.sqrt (K:ℝ)+4*Real.sqrt (e:ℝ))^2) ≤
      2/3-4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m))^2)

private theorem cost_of_covered_offset {m j : ℕ} (hm : 32 ≤ m)
    (h : coveredOffset m j) : (j:ℝ) ≤ 161*reachScale m := by
  obtain ⟨u,v,r,K,e,hu,hu2,root,uv,v2,hr,_,he,gate,fit,cap⟩ := h
  have hr0 := zero_lt_one.trans hr
  have hu0 := zero_lt_one.trans hu
  have hrv : r ≤ v :=
    (le_mul_of_one_le_right hr0.le (le_add_of_nonneg_right (pow_nonneg (inv_nonneg.mpr hr0.le) e))).trans gate
  let n := m+j
  have hn : 32 ≤ n := by dsimp only [n]; omega
  have r2 : r < 2 := hrv.trans_lt v2
  have root' : (2-u)*u^n=1 := root
  obtain ⟨d,_,_,shift,_⟩ := choose_delay n hn
  obtain ⟨hb,gate',_⟩ := parameters hn hu hu2 root' shift
  let b : ℝ := 2-1/(n:ℝ)
  change 1 < b at hb
  change b*(1+(b⁻¹)^d) ≤ u at gate'
  have bp := zero_lt_one.trans hb
  have bu : b ≤ u :=
    (le_mul_of_one_le_right bp.le (le_add_of_nonneg_right (pow_nonneg (inv_nonneg.mpr bp.le) d))).trans gate'
  have lower : (1/2:ℝ)*2^n ≤ u^n :=
    (band_ratio_power hn (le_refl n)).trans (pow_le_pow_left₀ bp.le bu n)
  have fitu : (r⁻¹)^(K+e) ≤ 2-u := fit.trans (sub_le_sub_left uv _)
  have support : u^n ≤ r^(K+e) := by
    have eq : 2-u = 1/u^n := (eq_div_iff (pow_pos hu0 n).ne').2 root'
    rw [eq, inv_pow, ←one_div] at fitu
    simpa only [one_mul] using (div_le_div_iff₀ (pow_pos hr0 _) (pow_pos hu0 _)).1 fitu
  have index : n ≤ K+e := by
    by_contra! small
    have step := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show K+e+1 ≤ n by omega)
    rw [pow_succ] at step
    have strict := pow_lt_pow_left₀ r2 hr0.le (show K+e ≠ 0 by omega)
    linarith only [lower, support, step, strict]
  have hm' : (32:ℝ) ≤ m := by exact_mod_cast hm
  have db0 : 0 ≤ delayBudget m := by
    have num : 0 ≤ Real.log (4*(m:ℝ)) := Real.log_nonneg (by linarith only [hm'])
    have den : 0 ≤ Real.log (3/2) := Real.log_nonneg (by norm_num)
    dsimp [delayBudget]; positivity
  have hp : 0 < Real.sqrt (K:ℝ)+4*Real.sqrt (e:ℝ) := by positivity
  have hs : (Real.sqrt (K:ℝ)+4*Real.sqrt (e:ℝ))^2 ≤
      (Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m))^2 := by
    apply le_of_not_gt
    intro big
    have small := div_lt_div_of_pos_left (by norm_num : (0:ℝ)<4)
      (show 0 < 9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m))^2 by positivity)
      (mul_lt_mul_of_pos_left big (by norm_num : (0:ℝ)<9))
    linarith only [cap,small]
  have realIdx : (m:ℝ)+j ≤ (K:ℝ)+e := by exact_mod_cast index
  apply le_trans _ (finite_reach_le_scale hm)
  nlinarith only [realIdx, hs, Real.sq_sqrt (Nat.cast_nonneg K : 0≤(K:ℝ)),
    Real.sq_sqrt (Nat.cast_nonneg e : 0≤(e:ℝ)), Real.sq_sqrt db0,
    Real.sq_sqrt (show 0≤(m:ℝ)+2 by positivity), Nat.cast_nonneg (α:=ℝ) e,
    mul_nonneg (Real.sqrt_nonneg (K:ℝ)) (Real.sqrt_nonneg (e:ℝ))]

/-- The largest offset admitting a certificate, including certificates
transported left by monotonicity, has order sqrt(m log m). -/
theorem optimal_band_reach {m : ℕ} (hm : 32 ≤ m) :
    ∃ R : ℕ, IsGreatest {j : ℕ | coveredOffset m j} R ∧
      reachScale m / 4 ≤ (R:ℝ) ∧ (R:ℝ) ≤ 161 * reachScale m := by
  classical
  obtain ⟨d,_,_,shift,_,B,margin,_,lower⟩ := square_root_band_reach hm
  obtain ⟨j,size,small⟩ := exists_scale_offset hm shift
  obtain ⟨K,e,r,hK,he,hr,_,_,_,cost,_,atRoot⟩ := lower j small
  obtain ⟨roots,_,_,rootdata⟩ := FullRankWindow.jumps_along_finite_models
  let k := m+j-2
  have idx : k+2=m+j := by dsimp [k]; omega
  obtain ⟨hu,hu2,root,_⟩ := rootdata k
  rw [idx] at root
  obtain ⟨gate,fit,_⟩ := atRoot (roots k) hu hu2 root
  have witness : coveredOffset m j :=
    ⟨roots k,roots k,r,K,e,hu,hu2,root,le_rfl,hu2,hr,hK,he,gate,fit,cost.trans margin.le⟩
  let N := ⌈161 * reachScale m⌉₊
  have bounded (k : ℕ) (covered : coveredOffset m k) : k ≤ N := by
    exact_mod_cast (cost_of_covered_offset hm covered).trans (Nat.le_ceil _)
  let R := Nat.findGreatest (coveredOffset m) N
  have hit : coveredOffset m R := Nat.findGreatest_spec (bounded j witness) witness
  have top (k : ℕ) (hk : coveredOffset m k) : k ≤ R := Nat.le_findGreatest (bounded k hk) hk
  refine ⟨R, ⟨hit,fun k inSet => top k inSet⟩, ?_, cost_of_covered_offset hm hit⟩
  exact size.trans (by exact_mod_cast top j witness)

#print axioms optimal_band_reach
end MultinacciBands
