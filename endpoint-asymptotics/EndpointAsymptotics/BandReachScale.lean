import EndpointAsymptotics.MultinacciPopulationCap

noncomputable section
namespace MultinacciBands

/-- Natural scale for the number of additional multinacci indices reached. -/
def reachScale (m : ℕ) : ℝ := Real.sqrt ((m:ℝ)*Real.log m)

private theorem log_m_bounds {m : ℕ} (hm : 32 ≤ m) :
    1/2 ≤ Real.log m ∧ Real.log m ≤ m := by
  have h : (32:ℝ) ≤ m := by exact_mod_cast hm
  have tw := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at tw
  have hi := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith only [h] : (2:ℝ) ≤ m)
  have endval := Real.log_le_sub_one_of_pos (by linarith only [h] : (0:ℝ) < m)
  constructor <;> linarith only [hi,tw,endval]

/-- Rounding the half-scale down still gives at least a quarter-scale,
and the resulting offset satisfies the finite window condition. -/
theorem exists_scale_offset {m d : ℕ} (hm : 32 ≤ m)
    (shift : 4*(m:ℝ) ≤ (3/2:ℝ)^d) :
    ∃ j : ℕ, reachScale m / 4 ≤ (j:ℝ) ∧ 4*j^2 ≤ m*d := by
  have h : (32:ℝ) ≤ m := by exact_mod_cast hm
  have mp : 0 < (m:ℝ) := by linarith only [h]
  have ⟨lo,_⟩ := log_m_bounds hm
  have logd := Real.log_le_log (show 0 < 4*(m:ℝ) by positivity) shift
  rw [Real.log_pow] at logd
  have hdot := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3/2)
  have logle := Real.log_le_log mp (show (m:ℝ) ≤ 4*m by linarith only [mp])
  have ld : Real.log m ≤ d := by
    have q := mul_le_mul_of_nonneg_left hdot (Nat.cast_nonneg d)
    linarith only [q,logd,logle,Nat.cast_nonneg (α:=ℝ) d]
  have mass : (16:ℝ) ≤ (m:ℝ)*Real.log m := by
    linarith only [mul_le_mul h lo (by norm_num) mp.le]
  have nonneg : 0 ≤ reachScale m := Real.sqrt_nonneg _
  have sqr : (reachScale m)^2=(m:ℝ)*Real.log m := Real.sq_sqrt (by linarith only [mass])
  have large : (4:ℝ) ≤ reachScale m := (sq_le_sq₀ (by norm_num) nonneg).mp (by nlinarith only [sqr,mass])
  let j := ⌊reachScale m/2⌋₊
  have below : (j:ℝ) ≤ reachScale m/2 := Nat.floor_le (by positivity)
  have above : reachScale m/2 < (j:ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨j,by linarith only [above,large], ?_⟩
  have realbd := pow_le_pow_left₀ (Nat.cast_nonneg j : (0:ℝ) ≤ j) below 2
  have hprod := mul_le_mul_of_nonneg_left ld mp.le
  exact_mod_cast (show 4*(j:ℝ)^2 ≤ (m:ℝ)*d by nlinarith only [realbd,sqr,hprod])

theorem finite_reach_le_scale {m : ℕ} (hm : 32 ≤ m) :
    2 + 8*Real.sqrt ((m:ℝ)+2)*Real.sqrt (delayBudget m) + 16*delayBudget m
      ≤ 161*reachScale m := by
  have h : (32:ℝ) ≤ m := by exact_mod_cast hm
  have mp : 0<(m:ℝ) := by linarith only [h]
  obtain ⟨lo,hi⟩ := log_m_bounds hm
  have L : 0 ≤ Real.log m := by linarith only [lo]
  have denom := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<3/2)
  norm_num at denom
  have log4 := Real.log_le_log (by norm_num : (0:ℝ)<4) (by linarith only [h] : (4:ℝ) ≤ m)
  have db : delayBudget m ≤ 8*Real.log m := by
    have d0 : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
    have num : Real.log (4*(m:ℝ)) ≤ 2*Real.log m := by
      rw [Real.log_mul (by norm_num) mp.ne']; linarith only [log4]
    have p := mul_le_mul_of_nonneg_left denom (show 0≤6*Real.log m by positivity)
    have rat : Real.log (4*(m:ℝ))/Real.log (3/2) ≤ 6*Real.log m :=
      (div_le_iff₀ d0).2 (by linarith only [p,num])
    dsimp [delayBudget]; linarith only [rat,lo]
  have db0 : 0 ≤ delayBudget m := by
    have num : 0 ≤ Real.log (4*(m:ℝ)) := Real.log_nonneg (by linarith only [h])
    have den : 0 ≤ Real.log (3/2) := Real.log_nonneg (by norm_num)
    dsimp [delayBudget]; positivity
  have ts := Real.sq_sqrt (mul_nonneg mp.le L)
  change (reachScale m)^2 = (m:ℝ)*Real.log m at ts
  have t0 : 0 ≤ reachScale m := Real.sqrt_nonneg _
  have lbt : Real.log m ≤ reachScale m := (sq_le_sq₀ L t0).mp (by nlinarith only [ts,mul_le_mul_of_nonneg_right hi L])
  have two : 2 ≤ reachScale m := (sq_le_sq₀ (by norm_num) t0).mp (by nlinarith only [ts,mul_le_mul h lo (by norm_num) mp.le])
  have left : (m:ℝ)+2 ≤ 2*m := by linarith only [h]
  have prod := mul_le_mul left db db0 (show 0 ≤ 2*(m:ℝ) by positivity)
  have bound : Real.sqrt ((m:ℝ)+2)*Real.sqrt (delayBudget m) ≤ 4*reachScale m := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ (m:ℝ)+2),Real.sq_sqrt db0,ts]
    linarith only [prod]
  linarith only [bound,db,lbt,two]

end MultinacciBands
