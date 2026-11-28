import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EndpointAsymptotic
open Finset
open scoped BigOperators
noncomputable section

/-- Geometric normalized band endpoints; related to the logarithmic depth. -/
def edge (r : ℝ) (i : ℕ) : ℝ := 1-(r⁻¹)^i

theorem geometry {r c : ℝ} (hr : 1<r) (hc : c≤2) (d i : ℕ)
    (h : r*(1+(r⁻¹)^d)≤c) :
    c*edge r (i+1) ≤ edge r i+edge r (i+d) := by
  have hr0 : 0<r := by linarith
  have gate : 0≤c*r⁻¹-1-(r⁻¹)^d := by
    have ht : 1+(r⁻¹)^d≤c/r := (le_div_iff₀ hr0).2 (by linarith)
    rw [div_eq_mul_inv] at ht
    linarith only [ht]
  dsimp [edge]
  rw [pow_succ,pow_add]
  nlinarith only [hc,mul_nonneg (pow_nonneg (inv_nonneg.mpr hr0.le) i) gate]

theorem median_fails {r c z x y w : ℝ} (hr : 1<r) (hc : 0≤c) (hc2 : c≤2)
    (hz : 0≤z) (d i : ℕ) (h : r*(1+(r⁻¹)^d)≤c)
    (hx : edge r i*z≤x) (hy : y≤edge r (i+1)*z) (hw : edge r (i+d)*z≤w) :
    c*y ≤ x+w := by
  have hh := mul_le_mul_of_nonneg_right (geometry hr hc2 d i h) hz
  have hhy := mul_le_mul_of_nonneg_left hy hc
  nlinarith only [hh,hhy,hx,hw]

/-- After centering a terminal interval in [0,1], its effective coefficient
is bounded away from two by the original defect divided by the width. -/
theorem terminal_translation {c η y₁ y₂ y₃ : ℝ} (hc : c<2) (hη : 0<η)
    (hη1 : η≤1) (hy : y₃≤1)
    (h : (1-η+η*y₁)+(1-η+η*y₂) < c*(1-η+η*y₃)) :
    y₁+y₂ < (2-(2-c)/η)*y₃ := by
  apply (mul_lt_mul_left hη).1
  have eq : η*((2-(2-c)/η)*y₃)=2*η*y₃-(2-c)*y₃ := by field_simp; ring
  rw [eq]
  nlinarith only [h,mul_nonneg (mul_nonneg (sub_nonneg.mpr hc.le) (sub_nonneg.mpr hη1)) (sub_nonneg.mpr hy)]

private theorem telescope (u : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range m, (u i-u (i+1)) = u 0-u m := by
  induction m with
  | zero => simp
  | succ m h => rw [sum_range_succ,h]; ring

private theorem integral_square {x y : ℝ} (hy : 0≤y) (hxy : y≤x) :
    4*((Real.sqrt x)^3-(Real.sqrt y)^3)^2 ≤ 9*(x-y)^2*x := by
  let a := Real.sqrt x
  let b := Real.sqrt y
  have ha : 0≤a := Real.sqrt_nonneg _
  have hb : 0≤b := Real.sqrt_nonneg _
  have hab : 0≤a-b := sub_nonneg.mpr (Real.sqrt_le_sqrt hxy)
  change 4*(a^3-b^3)^2 ≤ _
  rw [← show a^2=x from Real.sq_sqrt (hy.trans hxy), ← show b^2=y from Real.sq_sqrt hy]
  have h : 2*(a^3-b^3)≤3*(a^2-b^2)*a := by
    nlinarith only [mul_nonneg (sq_nonneg (a-b)) (show 0≤a+2*b by linarith)]
  have nn : 0≤2*(a^3-b^3) := by
    nlinarith only [mul_nonneg hab (show 0≤a^2+a*b+b^2 by positivity)]
  nlinarith only [mul_self_le_mul_self nn h]

/-- Finite Riemann-sum inequality, with the upper ε+q tail retained. -/
theorem quantile_square (K : ℕ) (T : ℕ → ℝ) (pos : ∀ i, 0≤T i)
    (down : ∀ i<K, T (i+1)≤T i) :
    4*((Real.sqrt (T 0))^3-(Real.sqrt (T K))^3)^2 ≤
      9*(K:ℝ)*∑ i ∈ range K, (T i-T (i+1))^2*T i := by
  let h (i : ℕ) := (Real.sqrt (T i))^3
  let g (i : ℕ) := h i - h (i+1)
  have terms := sum_le_sum (fun i (hi:i∈range K) => integral_square (pos (i+1)) (down i (mem_range.mp hi)))
  change (∑ i ∈ range K, 4*(g i)^2) ≤ _ at terms
  rw [←mul_sum] at terms
  have cs := sum_mul_sq_le_sq_mul_sq (range K) (fun _ => (1:ℝ)) g
  simp only [one_mul,one_pow,sum_const,card_range,nsmul_eq_mul,mul_one] at cs
  have summ : ∑ i ∈ range K, g i = h 0-h K := telescope h K
  rw [summ] at cs
  have hh : (∑ i ∈ range K, 9*(T i-T (i+1))^2*T i) =
      9*∑ i ∈ range K, (T i-T (i+1))^2*T i := by
    rw [mul_sum]
    apply sum_congr rfl; intro i _; ring
  rw [hh] at terms
  change 4*(h 0-h K)^2 ≤ _
  nlinarith only [mul_le_mul_of_nonneg_left terms (Nat.cast_nonneg K),cs]

/-- Quantile loss lower bound before taking the limits in r,d,ε. An upper
bound b on T_i-T_{i+d} isolates the error from the d adjacent geometric bands. -/
theorem finite_quantile_loss (K d : ℕ) (T : ℕ → ℝ) {ε H b : ℝ} (hε : 0<ε)
    (h0 : T 0=1) (pos : ∀ i, 0≤T i) (down : ∀ i<K, T (i+1)≤T i)
    (htail : ∀ i<K, ε≤T (i+d)) (slack : ∀ i<K, T i-T (i+d)≤b)
    (hb : 0≤b) (loss : ∑ i ∈ range K, (T i-T (i+1))^2*T (i+d) ≤ H) :
    4*(1-(Real.sqrt (T K))^3)^2 ≤ 9*(K:ℝ)*H*(1+b/ε) := by
  let a (i:ℕ) := T i-T (i+1)
  have L : ∑ i ∈ range K, (a i)^2 * T (i+d) ≤ H := loss
  have sq : (∑ i ∈ range K, (a i)^2)*ε ≤ H := by
    rw [sum_mul]
    apply le_trans _ L
    apply sum_le_sum; intro i hi
    exact mul_le_mul_of_nonneg_left (htail i (mem_range.mp hi)) (sq_nonneg _)
  have raw : (∑ i ∈ range K, (a i)^2*T i) ≤ H + (H/ε)*b := by
    have hsum : (∑ i ∈ range K, (a i)^2*T i) ≤
        ∑ i ∈ range K, ((a i)^2*T (i+d)+(a i)^2*b) := by
      apply sum_le_sum; intro i hi
      nlinarith only [mul_le_mul_of_nonneg_left (slack i (mem_range.mp hi)) (sq_nonneg (a i))]
    rw [sum_add_distrib, ← sum_mul] at hsum
    exact hsum.trans (add_le_add L (mul_le_mul_of_nonneg_right ((le_div_iff₀ hε).2 sq) hb))
  have q := quantile_square K T pos down
  rw [h0,Real.sqrt_one,one_pow] at q
  calc
    _ ≤ 9*(K:ℝ)*∑ i ∈ range K, (a i)^2*T i := q
    _ ≤ 9*(K:ℝ)*(H+(H/ε)*b) := mul_le_mul_of_nonneg_left raw (by positivity)
    _ = _ := by ring

#print axioms median_fails
#print axioms terminal_translation
#print axioms finite_quantile_loss
end
end EndpointAsymptotic
