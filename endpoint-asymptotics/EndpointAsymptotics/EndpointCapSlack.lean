import EndpointAsymptotics.MultinacciPopulationCap

open QuantitativeBands IidJumpSpectra

noncomputable section
namespace MultinacciBands

def canonicalDelay (m : ℕ) : ℕ := ⌈Real.log (4*(m:ℝ))/Real.log (3/2)⌉₊

def intervalCap (m : ℕ) : ℝ :=
  2/3-4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (canonicalDelay m))^2)

theorem delay_eq_canonical {m d : ℕ} (hm : 32 ≤ m)
    (lower : 4*(m:ℝ) ≤ (3/2:ℝ)^d) (upper : (d:ℝ) < delayBudget m) :
    d = canonicalDelay m := by
  have hp : 0 < (m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have count := Real.log_le_log (show 0 < 4*(m:ℝ) by positivity) lower
  rw [Real.log_pow] at count
  unfold canonicalDelay
  apply le_antisymm
  · have high := add_le_add_right (Nat.le_ceil (Real.log (4*(m:ℝ))/Real.log (3/2))) (1:ℝ)
    have b := upper.trans_le high
    exact Nat.lt_succ_iff.mp (show d < ⌈Real.log (4*(m:ℝ))/Real.log (3/2)⌉₊+1 by exact_mod_cast b)
  · exact Nat.ceil_le.mpr ((div_le_iff₀ (Real.log_pos (by norm_num))).2 count)

/-- The same quantile bands give a strictly sharper uniform cap throughout
an explicit interval extending past the root. -/
theorem explicit_right_interval_strict_cap {m : ℕ} {c : ℝ} (hm : 32 ≤ m)
    (hc : 1 < c) (hc2 : c < 2) (root : (2 - c) * c ^ m = 1) :
    ∃ B < 2/3 - 4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m))^2),
      B = intervalCap m ∧ ∀ x ∈ Set.Icc c (2 - (2-c)/(4*(m:ℝ))), extremal 2 x ≤ B := by
  obtain ⟨d, hd, _, shift, hlog⟩ := choose_delay m hm
  let r : ℝ := 2 - 1/(m:ℝ)
  obtain ⟨hr, gate, fit⟩ := parameters hm hc hc2 root shift
  change 1 < r at hr
  change r*(1+(r⁻¹)^d) ≤ c at gate
  change (r⁻¹)^(m+2) ≤ 2-c at fit
  have hr0 := zero_lt_one.trans hr
  have hp : 0 < r⁻¹ := inv_pos.mpr hr0
  have hm' : (32:ℝ) ≤ m := by exact_mod_cast hm
  have mp : 0 < (m:ℝ) := by linarith only [hm']
  have rlo : (3/2:ℝ) ≤ r := by
    have inv : 1/(m:ℝ) ≤ 1/2 := (div_le_iff₀ mp).2 (by linarith only [hm'])
    dsimp only [r]
    linarith only [inv]
  have rd : 4*(m:ℝ) ≤ r^d :=
    shift.trans (pow_le_pow_left₀ (by norm_num) rlo d)
  have id : (r⁻¹)^d ≤ 1/(4*(m:ℝ)) := by
    rw [inv_pow, ←one_div]
    exact one_div_le_one_div_of_le (by positivity) rd
  have width : (r⁻¹)^(m+2+d) ≤ (2-c)/(4*(m:ℝ)) := by
    rw [pow_add, div_eq_mul_one_div]
    exact mul_le_mul fit id (pow_nonneg hp.le _) (sub_nonneg.mpr hc2.le)
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hd
  have hden : Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (d:ℝ) <
      Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m) :=
    add_lt_add_left (mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hd0.le hlog) (by norm_num)) _
  have hpos : 0 < Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (d:ℝ) := by positivity
  refine ⟨2/3-4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (d:ℝ))^2), ?_, ?_, ?_⟩
  · apply sub_lt_sub_left
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hden hpos.le (by decide : (2:ℕ) ≠ 0)) (by norm_num)
  · unfold intervalCap
    rw [←delay_eq_canonical hm shift hlog]
  · intro x hx
    have xbound := hx.2
    have pos : 0 < (2-c)/(4*(m:ℝ)) := div_pos (sub_pos.mpr hc2) (by positivity)
    have cap := population_band_upper (m+2) d hd hr (by linarith only [pos, xbound] : x<2)
      (gate.trans hx.1) (by linarith only [width,xbound])
    simpa using cap

/-- In particular, there is a nonzero right-hand neighborhood on which
the explicit upper bound at the root has a fixed positive margin. -/
theorem right_neighborhood_strict_cap {m : ℕ} {c : ℝ} (hm : 32 ≤ m)
    (hc : 1 < c) (hc2 : c < 2) (root : (2 - c) * c ^ m = 1) :
    ∃ ε > 0, ∃ B < 2/3 - 4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m))^2),
      ∀ x ∈ Set.Icc c (c+ε), extremal 2 x ≤ B := by
  obtain ⟨B, margin, _, upper⟩ := explicit_right_interval_strict_cap hm hc hc2 root
  have hm' : (32:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < 2-c := sub_pos.mpr hc2
  have shrink : (2-c)/(4*(m:ℝ)) < 2-c :=
    div_lt_self hp (by linarith only [hm'])
  refine ⟨2-c-(2-c)/(4*(m:ℝ)), by linarith, B, margin, ?_⟩
  intro x hx
  exact upper x ⟨hx.1, by linarith only [hx.2]⟩

/-- Up to m factors of 2−1/m cost at most a factor of two relative to 2.
This is Bernoulli's inequality at the two exponents used below. -/
theorem band_ratio_power {m k : ℕ} (hm : 32 ≤ m) (hk : k ≤ m) :
    (1/2:ℝ)*2^k ≤ (2-1/(m:ℝ))^k := by
  let r : ℝ := 2-1/(m:ℝ)
  have hm' : (32:ℝ) ≤ m := by exact_mod_cast hm
  have hk' : (k:ℝ) ≤ m := by exact_mod_cast hk
  have mp : 0 < (m:ℝ) := by linarith only [hm']
  have inv : 1/(m:ℝ) ≤ 1/2 := (div_le_iff₀ mp).2 (by linarith only [hm'])
  have rlo : 3/2 ≤ r := by dsimp only [r]; linarith only [inv]
  have bern := one_add_mul_sub_le_pow (show -1 ≤ r/2 by linarith only [rlo]) k
  have id : 1+(k:ℝ)*(r/2-1)=1-(k:ℝ)/(2*m) := by dsimp only [r]; field_simp; ring
  have half : (k:ℝ)/(2*m) ≤ 1/2 :=
    (div_le_iff₀ (by positivity)).2 (by linarith only [hk'])
  rw [id, div_pow] at bern
  exact (le_div_iff₀ (by positivity)).mp (le_trans (by linarith only [half]) bern)

/-- A single cap is valid throughout each indicated candidate's right
neighborhood. The number of covered root indices equals the ceiling of
log(4m)/log(3/2), including the starting root. -/
theorem logarithmic_run_strict_cap {m : ℕ} {c : ℝ} (hm : 32 ≤ m)
    (hc : 1 < c) (hc2 : c < 2) (root : (2-c)*c^m = 1) :
    ∃ B < 2/3 - 4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m))^2),
      ∀ (j : ℕ), (j:ℝ) < Real.log (4*(m:ℝ))/Real.log (3/2) →
      ∀ (u : ℝ), 1 < u → u < 2 → (2-u)*u^(m+j) = 1 →
        c ≤ u ∧ ∃ ε > 0, ∀ x ∈ Set.Icc c (u+ε), extremal 2 x ≤ B := by
  classical
  obtain ⟨d, hd, dm, shift, hlog⟩ := choose_delay m hm
  let r : ℝ := 2-1/(m:ℝ)
  obtain ⟨hr, gate, _⟩ := parameters hm hc hc2 root shift
  change 1 < r at hr
  change r*(1+(r⁻¹)^d) ≤ c at gate
  have hr0 := zero_lt_one.trans hr
  have hm' : (32:ℝ) ≤ m := by exact_mod_cast hm
  have mp : 0 < (m:ℝ) := by linarith only [hm']
  have inv : 1/(m:ℝ) ≤ 1/2 := (div_le_iff₀ mp).2 (by linarith only [hm'])
  have rlo : 3/2 ≤ r := by dsimp only [r]; linarith only [inv]
  have rsq : 2 ≤ r^2 := (by norm_num : (2:ℝ) ≤ (3/2)^2).trans
    (pow_le_pow_left₀ (by norm_num) rlo 2)
  have enclosure : (2:ℝ)^m ≤ r^(m+2) := by
    rw [pow_add]
    have half := band_ratio_power hm (le_refl m)
    change (1/2:ℝ)*2^m ≤ r^m at half
    linarith only [half, mul_le_mul_of_nonneg_left rsq (pow_nonneg hr0.le m)]
  have logd := Real.log_le_log (show 0 < 4*(m:ℝ) by positivity) shift
  rw [Real.log_pow] at logd
  have depth : Real.log (4*(m:ℝ))/Real.log (3/2) ≤ d :=
    (div_le_iff₀ (Real.log_pos (by norm_num))).2 logd
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hd
  have hden : Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (d:ℝ) <
      Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m) :=
    add_lt_add_left (mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hd0.le hlog) (by norm_num)) _
  have hpos : 0 < Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (d:ℝ) := by positivity
  refine ⟨2/3-4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (d:ℝ))^2), ?_, ?_⟩
  · apply sub_lt_sub_left
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hden hpos.le (by decide : (2:ℕ) ≠ 0)) (by norm_num)
  intro j hj u hu hu2 ru
  have jd : j < d := by exact_mod_cast (hj.trans_le depth)
  have npos : m+j ≠ 0 := by omega
  have hu0 := zero_lt_one.trans hu
  have order : c ≤ u := by
    by_contra! small
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero npos
    change m+j = k+1 at hk
    have en : (2-u)*u^(k+1)=1 := by simpa only [←hk] using ru
    have opened := FullRankWindow.threshold_opens_right hu small en
    rw [←hk] at opened
    have ge := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hc.le (show m ≤ m+j by omega)) (sub_nonneg.mpr hc2.le)
    linarith only [opened, ge, root]
  have tail : (2:ℝ)^j ≤ r^d := by
    have p := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show j+1 ≤ d by omega)
    rw [pow_succ] at p
    have half := band_ratio_power hm dm
    change (1/2:ℝ)*2^d ≤ r^d at half
    linarith only [p, half]
  have prod : u^(m+j) < r^(m+2+d) := calc
    u^(m+j) < (2:ℝ)^(m+j) := pow_lt_pow_left₀ hu2 hu0.le npos
    _ = (2:ℝ)^m * 2^j := pow_add _ _ _
    _ ≤ r^(m+2) * r^d := mul_le_mul enclosure tail (by positivity) (by positivity)
    _ = r^(m+2+d) := (pow_add _ _ _).symm
  let width := (r⁻¹)^(m+2+d)
  have gap : width < 2-u := by
    have equ : 2-u = 1/u^(m+j) := (eq_div_iff (pow_pos hu0 _).ne').mpr ru
    dsimp only [width]
    rw [equ, inv_pow, ←one_div]
    exact one_div_lt_one_div_of_lt (pow_pos hu0 _) prod
  have wp : 0 < width := pow_pos (inv_pos.mpr hr0) _
  refine ⟨order, 2-width-u, by linarith only [gap], ?_⟩
  intro x hx
  have xb := hx.2
  have cap := population_band_upper (m+2) d hd hr (by linarith only [wp,xb] : x<2)
    (gate.trans hx.1) (show width ≤ 2-x by linarith only [xb])
  simpa using cap

#print axioms explicit_right_interval_strict_cap
#print axioms right_neighborhood_strict_cap
#print axioms logarithmic_run_strict_cap
end MultinacciBands
