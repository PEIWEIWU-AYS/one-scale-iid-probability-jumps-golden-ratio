import EndpointAsymptotics.QuantileAssembly
import EndpointAsymptotics.FiniteBandLoss
import EndpointAsymptotics.TerminalIntervalLoss
import EndpointAsymptotics.QuantileBounds
open Finset OneScale EndpointAsymptotic IidJumpSpectra IidInfiniteJumps
open scoped BigOperators
noncomputable section
namespace QuantitativeBands

/-- All-support bound, with an explicit deficit, under the two numerical
conditions on the geometric bands. The supremum is over nonnegative Borel laws. -/
theorem population_band_upper (K d : ℕ) (hd : 0<d) {r c : ℝ} (hr : 1<r) (hc2 : c<2)
    (gate : r*(1+(r⁻¹)^d)≤c) (fit : (r⁻¹)^(K+d)≤2-c) :
    extremal 2 c ≤ 2/3-4/(9*(Real.sqrt K+4*Real.sqrt d)^2) := by
  classical
  have hr0 : 0<r := zero_lt_one.trans hr
  have invle : r⁻¹≤1 := by rw [←one_div];exact (div_le_iff₀ hr0).2 (by linarith)
  have hc : 1<c := by nlinarith only [hr,gate,mul_nonneg hr0.le (pow_nonneg (inv_nonneg.mpr hr0.le) d)]
  have hd' : 1≤(d:ℝ) := by exact_mod_cast hd
  apply population_of_positive_cap
  intro n x w hx hw
  let H := 2/3-score c x w
  have positive : 0<H := by
    obtain ⟨μ,hμ,_,val⟩ := weighted_law c x w (fun i => (hx i).le) hw
    haveI := hμ
    have low := (inverse_log_bounds hc hc2).1
    have hs : score c x w ≤ extremal 2 c := val ▸ iidWin_le_extremal 2 c μ
    have hh := logDepth_pos hc hc2
    dsimp only [H]; linarith [show 0 < 1/(3*(logDepth c+1)) by positivity]
  apply band_cap_of_root_bound K d hd (H:=H) rfl positive.le
  apply finite_quantile_assembly K d hd x w hx hw H positive
  intro z hz
  let t (i : ℕ) := edge r i*z
  have mt : Monotone t := by
    intro i j h
    exact mul_le_mul_of_nonneg_right (sub_le_sub_left
      (pow_le_pow_of_le_one (inv_nonneg.mpr hr0.le) invle h) 1) hz.le
  have geom (i : ℕ) : c*t (i+1) ≤ t i+t (i+d) := by
    have g := mul_le_mul_of_nonneg_right (geometry hr hc2.le d i gate) hz.le
    simpa only [t,add_mul,mul_assoc] using g
  have bound (i : ℕ) : t i≤z := by
    have h := mul_nonneg (pow_nonneg (inv_nonneg.mpr hr0.le) i) hz.le
    dsimp [t,edge];linarith
  have loss := finite_band_loss (K+d) d hd (zero_lt_one.trans hc) hc2.le x w
    (fun i => (hx i).le) hw t mt geom
  refine ⟨t,mt,by simp [t,edge],bound,loss,?_⟩
  let u (i : Fin n) := if t K≤x i ∧ x i≤z then w i else 0
  have hu (i) : 0≤u i := by dsimp [u];split_ifs;exact hw.1 i; rfl
  have uw (i) : u i≤w i := by dsimp [u];split_ifs; rfl;exact hw.1 i
  have inside (i) (hi : u i≠0) : (1-(r⁻¹)^K)*z≤x i ∧ x i≤z := by
    by_contra no
    exact hi (if_neg (show ¬(t K≤x i ∧ x i≤z) from no))
  have cap := TerminalRescaling.terminal_mass_bound K d hr hc2 hz.le gate fit x w u
    (fun i => (hx i).le) hw hu uw inside
  have mass : bandWeight w (fun j => t K≤x j ∧ x j≤z) = ∑ i,u i := by
    unfold bandWeight
    rw [sum_filter]
    apply sum_congr rfl; intro j _
    by_cases h : t K≤x j ∧ x j≤z <;> simp only [u, h, if_true, if_false]
  rw [mass]
  exact cap.trans (mul_le_mul_of_nonneg_right (by linarith only [hd']) positive.le)

#print axioms population_band_upper
end QuantitativeBands
