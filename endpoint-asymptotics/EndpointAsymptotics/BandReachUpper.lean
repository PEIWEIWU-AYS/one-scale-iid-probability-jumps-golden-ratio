import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace MultinacciBands

/-- A single feasible band certificate at the root of index m+j can beat
the comparison bound with parameter D only within this many indices. -/
theorem band_reach_upper {m j K e : ℕ} {r u D : ℝ}
    (hm : 0 < m) (he : 0 < e) (hD : 0 ≤ D) (hr : 1 < r) (hu : 1 < u)
    (root : (2-u)*u^(m+j) = 1)
    (gate : r*(1+(r⁻¹)^e) ≤ u) (fit : (r⁻¹)^(K+e) ≤ 2-u)
    (cap : 2/3-4/(9*(Real.sqrt (K:ℝ)+4*Real.sqrt (e:ℝ))^2)
      ≤ 2/3-4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt D)^2)) :
    (j:ℝ) < 2 + 8 * Real.sqrt ((m:ℝ)+2) * Real.sqrt D + 16*D := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hru : r < u := by
    nlinarith only [gate, mul_pos hr0 (pow_pos (inv_pos.mpr hr0) e)]
  have hpow : u^(m+j) ≤ r^(K+e) := by
    have eq : 2-u = 1/u^(m+j) := (eq_div_iff (pow_pos hu0 _).ne').2 root
    rw [eq, inv_pow, ←one_div] at fit
    simpa only [one_mul] using (div_le_div_iff₀ (pow_pos hr0 _) (pow_pos hu0 _)).1 fit
  have hidx : m+j < K+e := by
    apply lt_of_not_ge
    intro bad
    have h₁ := pow_le_pow_right₀ hr.le bad
    have h₂ := pow_lt_pow_left₀ hru hr0.le (show m+j ≠ 0 by omega)
    exact (not_lt_of_ge hpow) (h₁.trans_lt h₂)
  have hp : 0 < Real.sqrt (K:ℝ)+4*Real.sqrt (e:ℝ) := by positivity
  have hq : 0 < Real.sqrt ((m:ℝ)+2)+4*Real.sqrt D := by positivity
  have hs : (Real.sqrt (K:ℝ)+4*Real.sqrt (e:ℝ))^2 ≤
      (Real.sqrt ((m:ℝ)+2)+4*Real.sqrt D)^2 := by
    apply le_of_not_gt
    intro h
    have hdiv := div_lt_div_of_pos_left (by norm_num : (0:ℝ)<4)
      (show 0 < 9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt D)^2 by positivity)
      (mul_lt_mul_of_pos_left h (by norm_num : (0:ℝ)<9))
    linarith only [cap,hdiv]
  have hreal : (m:ℝ)+j < (K:ℝ)+e := by exact_mod_cast hidx
  nlinarith only [hreal, hs, Real.sq_sqrt (show 0 ≤ (K:ℝ) by positivity),
    Real.sq_sqrt (show 0 ≤ (e:ℝ) by positivity), Real.sq_sqrt hD,
    Real.sq_sqrt (show 0 ≤ (m:ℝ)+2 by positivity),
    mul_nonneg (Real.sqrt_nonneg (K:ℝ)) (Real.sqrt_nonneg (e:ℝ)), Nat.cast_nonneg (α:=ℝ) e]

#print axioms band_reach_upper
end MultinacciBands
