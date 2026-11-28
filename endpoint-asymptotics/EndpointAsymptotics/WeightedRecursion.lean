import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter Finset
open scoped Topology BigOperators
namespace EndpointRecursion
noncomputable section

/-- Inner minimization for a weighted total-order ladder after deleting its
bottom atom. The argument is the remaining mass. -/
theorem bellman_min {A : ℝ} (hA : 1/3<A) :
    IsLeast ((fun t : ℝ => 1-t+A*t^3) '' Set.Icc 0 1)
      (1-2/(3*Real.sqrt (3*A))) := by
  let s := Real.sqrt (3*A)
  have hsq : s^2=3*A := Real.sq_sqrt (by linarith)
  have hs : 1<s := by nlinarith [show 0≤s from Real.sqrt_nonneg _]
  have hs0 : 0<s := by linarith
  have hi : 3*A*(s⁻¹)^2=1 := by rw [← hsq]; field_simp
  have hval : 1-s⁻¹+A*(s⁻¹)^3 = 1-2/(3*s) := by
    field_simp
    nlinarith only [hsq]
  refine ⟨⟨s⁻¹,⟨inv_nonneg.mpr hs0.le,(inv_le_one₀ hs0).mpr hs.le⟩,hval⟩,?_⟩
  rintro _ ⟨t,ht,rfl⟩
  change 1-2/(3*s) ≤ _
  rw [←hval]
  have eq : (1-t+A*t^3)-(1-s⁻¹+A*(s⁻¹)^3) = A*(t-s⁻¹)^2*(t+2*s⁻¹) := by
    nlinarith only [congrArg (fun b : ℝ => b*(t-s⁻¹)) hi]
  apply sub_nonneg.mp; rw [eq]
  exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith [ht.1, inv_pos.mpr hs0])

/-- x_n is three times the optimal deficit on n+1 levels. -/
def x : ℕ → ℝ
  | 0 => 2
  | n+1 => 2*x n/(Real.sqrt (1+x n)*(1+Real.sqrt (1+x n)))

theorem xpos (n : ℕ) : 0<x n := by
  induction n with
  | zero => norm_num [x]
  | succ n ih => rw [x]; positivity

private def s (n : ℕ) := Real.sqrt (1+x n)

private theorem s_pos (n : ℕ) : 1<s n := by
  have h0 : 0≤s n := Real.sqrt_nonneg _
  have h : (s n)^2=1+x n := Real.sq_sqrt (by linarith [xpos n])
  nlinarith only [h0,h,xpos n]

/-- Difference of reciprocals with cancellation of the vanishing deficit. -/
theorem reciprocal_step (n : ℕ) : (x (n+1))⁻¹-(x n)⁻¹=(s n+2)/(2*(s n+1)) := by
  change (2*x n/(s n*(1+s n)))⁻¹ - _ = _
  have hs0 : 0<s n := by linarith [s_pos n]
  have hsq : (s n)^2=1+x n := Real.sq_sqrt (by linarith [xpos n])
  have hxn : x n≠0 := (xpos n).ne'
  field_simp
  nlinarith only [hsq,congrArg (fun a : ℝ => a*s n) hsq]

private theorem x_to_zero : Tendsto x atTop (𝓝 0) := by
  have lower (n : ℕ) : (n:ℝ)/2 ≤ (x n)⁻¹ := by
    induction n with
    | zero => norm_num [x]
    | succ n h =>
      have hs := s_pos n
      have half : (1:ℝ)/2≤(s n+2)/(2*(s n+1)) := (le_div_iff₀ (by linarith)).mpr (by linarith)
      push_cast
      linarith only [reciprocal_step n,h,half]
  have upper : ∀ᶠ n : ℕ in atTop, x n ≤ 2/(n:ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    apply (le_div_iff₀ hpos).2
    have lo := mul_le_mul_of_nonneg_right (lower n) (xpos n).le
    rw [inv_mul_cancel₀ (xpos n).ne'] at lo
    linarith
  exact squeeze_zero' (Eventually.of_forall fun n => (xpos n).le) upper (tendsto_const_div_atTop_nhds_zero_nat 2)

private theorem telescope (v : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range n, (v (i+1)-v i)=v n-v 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih];ring

theorem weighted_deficit_limit : Tendsto (fun n : ℕ => (n:ℝ)*(x n/3)) atTop (𝓝 (4/9)) := by
  have slim : Tendsto s atTop (𝓝 1) := by
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=(1:ℝ))).add x_to_zero)
    simpa [s,Function.comp_def] using ht
  have step : Tendsto (fun n : ℕ => (x (n+1))⁻¹-(x n)⁻¹) atTop (𝓝 (3/4)) := by
    simp_rw [reciprocal_step]
    have hl := (slim.add_const 2).div ((tendsto_const_nhds (x:=(2:ℝ))).mul (slim.add_const 1)) (by norm_num)
    convert hl using 1; norm_num
  have ces := step.cesaro
  simp_rw [telescope (fun i => (x i)⁻¹)] at ces
  have c0 := tendsto_const_div_atTop_nhds_zero_nat ((x 0)⁻¹)
  have csum := ces.add c0
  have lim : Tendsto (fun n : ℕ => (n:ℝ)⁻¹*(x n)⁻¹) atTop (𝓝 (3/4)) := by
    rw [add_zero] at csum
    apply csum.congr'
    exact Eventually.of_forall (fun n => by dsimp; ring)
  have inv := lim.inv₀ (by norm_num)
  have hd := inv.div_const 3
  convert hd using 1
  · ext n
    simp;ring
  · norm_num

#print axioms bellman_min
#print axioms weighted_deficit_limit
end
end EndpointRecursion
