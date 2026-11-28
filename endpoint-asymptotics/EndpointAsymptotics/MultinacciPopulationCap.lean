import EndpointAsymptotics.QuantilePopulationUpper
import EndpointAsymptotics.MultinacciBandParameters
open QuantitativeBands IidJumpSpectra
noncomputable section
namespace MultinacciBands

def delayBudget (m : ℕ) : ℝ := Real.log (4*(m:ℝ))/Real.log (3/2)+1

/-- The cap holds for arbitrary support cardinality at the exact critical
coefficient. Its right side has no free scale or rank parameters. -/
theorem unrestricted_upper {m : ℕ} {c : ℝ} (hm : 32≤m) (hc : 1<c) (hc2 : c<2)
    (root : (2-c)*c^m=1) :
    extremal 2 c ≤ 2/3-4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m))^2) := by
  obtain ⟨d,hd,dm,shift,logb⟩ := choose_delay m hm
  obtain ⟨hr,gate,fit⟩ := parameters hm hc hc2 root shift
  let K := m+2-d
  have kd : K+d=m+2 := by dsimp [K];omega
  rw [←kd] at fit
  have ub := population_band_upper K d hd hr hc2 gate fit
  apply ub.trans
  apply sub_le_sub_left
  have dk : 0<(d:ℝ) := by exact_mod_cast hd
  have hk : (K:ℝ)≤(m:ℝ)+2 := by exact_mod_cast (show K≤m+2 by dsimp [K];omega)
  have A : Real.sqrt K+4*Real.sqrt d ≤ Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m) :=
    add_le_add (Real.sqrt_le_sqrt hk) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt logb.le) (by norm_num))
  have hpos : 0<Real.sqrt K+4*Real.sqrt d := by positivity
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le A 2) (by norm_num)

#print axioms unrestricted_upper
end MultinacciBands
