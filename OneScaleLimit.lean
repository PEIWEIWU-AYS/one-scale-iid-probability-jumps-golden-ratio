import OneScaleMenu

open Finset
open scoped BigOperators
noncomputable section
namespace OneScale

private def band (c x : ℝ) : Fin 3 := if c*x < 2 then 0 else if c*c*x < c+2 then 1 else 2

private def charge (a b k : Fin 3) : ℝ :=
  if a=0 ∧ b=0 ∧ k≠0 then 1 else
  if a=0 ∧ b≠0 ∧ k≠0 ∧ (b≠1 ∨ k≠1) then 1 else
  if a=1 ∧ b=1 ∧ k=2 then 1 else 0

private lemma charge_nonnegative (a b k : Fin 3) : 0 ≤ charge a b k := by
  unfold charge; split_ifs <;> norm_num

private lemma band_cases {a b k : Fin 3} (hk : k ≠ 0)
    (hk' : k=1 → a=0 ∧ b=0) (ha : a=2 → b=0) (hb : b=2 → a=0) :
    1 ≤ charge a b k + charge b k a + charge k a b := by
  revert hk hk' ha hb
  fin_cases a <;> fin_cases b <;> fin_cases k <;> norm_num [charge, Fin.ext_iff]

private lemma is_win {c x y z : ℝ} (hc : 1 < c) (hφ : c*c < c+1)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : z < c) (hw : x+y < c*z) :
    x < z ∧ y < z ∧ 1 ≤ charge (band c x) (band c y) (band c z) +
      charge (band c y) (band c z) (band c x) + charge (band c z) (band c x) (band c y) := by
  classical
  have hcp : 0 < c := by linarith
  have hgap := mul_lt_mul_of_pos_left hz (sub_pos.mpr hc)
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hbig (x : ℝ) (h : band c x ≠ 0) : 2 ≤ c*x := by
    by_contra! hn
    exact h (by simp [band,hn])
  have hlarge (x : ℝ) (h : band c x = 2) : c+2 ≤ c*c*x := by
    by_contra! hn
    by_cases hlow : c*x<2
    · simp [band,hlow,Fin.ext_iff] at h
    · simp [band,hlow,hn,Fin.ext_iff] at h
  have hmiddle (x : ℝ) (h : band c x = 1) : c*c*x < c+2 := by
    by_contra! hn
    by_cases hlow : c*x<2
    · simp [band,hlow,Fin.ext_iff] at h
    · simp [band,hlow,not_lt.mpr hn,Fin.ext_iff] at h
  have hpow : c^4 < 3*c+2 := by
    have h1 : c^2+c+2 > 0 := by positivity
    nlinarith [mul_pos (show 0 < c+1-c*c by linarith) h1]
  have hcs := mul_lt_mul_of_pos_left hw hcp
  have hcc := mul_lt_mul_of_pos_left hw (mul_pos hcp hcp)
  have hcz := mul_lt_mul_of_pos_left hz (show 0 < c*c*c by positivity)
  have impossible (x y : ℝ) (h : c*c*(x+y) < c*c*(c*z))
      (hx' : band c x=2) (hy' : band c y≠0) : False := by
    have P := hlarge x hx'
    have Q := mul_le_mul_of_nonneg_left (hbig y hy') hcp.le
    nlinarith
  apply band_cases
  · have h : ¬ c*z < 2 := by linarith
    simp [band,h]
    split_ifs <;> decide
  · intro h
    have M := hmiddle z h
    constructor <;> by_contra hn
    · have H := hbig _ hn
      nlinarith [mul_le_mul_of_nonneg_left hy hcp.le]
    · have H := hbig _ hn
      nlinarith [mul_le_mul_of_nonneg_left hx hcp.le]
  · intro h; by_contra hn
    exact impossible x y hcc h hn
  · intro h; by_contra hn
    exact impossible y x (by simpa only [add_comm y x] using hcc) h hn

private def indicator {α : Type*} (c : ℝ) (x : α → ℝ) (i j k : α) : ℝ :=
  by classical exact if Win c x i j k then 1 else 0

private lemma triple_bound {α : Type*} {x : α → ℝ} {c : ℝ}
    (hc : 1 < c) (hφ : c*c < c+1) (hx : Cfg c x) (i j k : α) :
    indicator c x i j k + indicator c x j k i + indicator c x k i j ≤
    charge (band c (x i)) (band c (x j)) (band c (x k)) +
    charge (band c (x j)) (band c (x k)) (band c (x i)) +
    charge (band c (x k)) (band c (x i)) (band c (x j)) := by
  have p {i j k : α} (h : Win c x i j k) :=
    is_win hc hφ (hx i).1 (hx j).1 (hx k).2 h
  unfold indicator
  split_ifs with h₁ h₂ h₃ h₃ h₂ h₃ h₃ <;> first
    | exfalso; linarith [(p h₁).1, (p h₂).2.1]
    | exfalso; linarith [(p h₁).2.1, (p h₃).1]
    | exfalso; linarith [(p h₂).1, (p h₃).2.1]
    | linarith [(p h₁).2.2]
    | linarith [(p h₂).2.2]
    | linarith [(p h₃).2.2]
    | linarith [charge_nonnegative (band c (x i)) (band c (x j)) (band c (x k)),
        charge_nonnegative (band c (x j)) (band c (x k)) (band c (x i)),
        charge_nonnegative (band c (x k)) (band c (x i)) (band c (x j))]

private lemma rotation {α : Type*} [Fintype α] (f : α → α → α → ℝ) :
    (∑ i, ∑ j, ∑ k, (f i j k + f j k i + f k i j)) = 3 * ∑ i, ∑ j, ∑ k, f i j k := by
  have rot (g : α → α → α → ℝ) : (∑ i, ∑ j, ∑ k, g j k i) = ∑ i, ∑ j, ∑ k, g i j k := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]
  have h := rot (fun i j k => f k i j)
  simp only at h
  rw [rot f, ← h]
  ring

private lemma pushed {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq γ]
    (e : α → γ) (w : α → ℝ) (g : γ → ℝ) :
    (∑ b, push e w b * g b) = ∑ i, w i * g (e i) := by
  classical
  simp only [push, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

private lemma poly_quarter (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    t^2*(1-t) + t*((1-t)^2-u^2) + u^2*(1-t-u) ≤ 1/4 := by
  by_cases hz : 1-2*t ≤ 0
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u) (show 1-2*t-u ≤ 0 by linarith),
       sq_nonneg (2*t-1)]
  · let z := 1-2*t
    have hz0 : 0 ≤ z := by dsimp [z]; linarith
    have hz1 : z ≤ 1 := by dsimp [z]; linarith
    have fact := mul_nonneg (sq_nonneg (3*u-2*z)) (show 0 ≤ 3*u+z by linarith)
    have z3 := mul_nonneg (sub_nonneg.mpr hz1) (sq_nonneg z)
    have h₁ : u^2*(z-u) ≤ 4*z^3/27 := by linear_combination fact / 27
    have : u^2*(z-u) ≤ z^2/4 := by
      linear_combination h₁ + (4/27)*z3 + (11/108)*(sq_nonneg z)
    dsimp [z] at this
    nlinarith

/-- The probability on one scale is at most one quarter below the golden ratio. -/
theorem score_le_quarter {α : Type*} [Fintype α] {c : ℝ} {x w : α → ℝ}
    (hc : 1 < c) (hφ : c*c < c+1) (hx : Cfg c x) (hw : Mass w) : score c x w ≤ 1/4 := by
  classical
  let e i := band c (x i)
  let f (i j k : α) := w i*w j*w k*indicator c x i j k
  let g (i j k : α) := w i*w j*w k*charge (e i) (e j) (e k)
  have point (i j k) : f i j k + f j k i + f k i j ≤ g i j k + g j k i + g k i j := by
    have h := mul_le_mul_of_nonneg_left (triple_bound hc hφ hx i j k)
      (mul_nonneg (mul_nonneg (hw.1 i) (hw.1 j)) (hw.1 k))
    dsimp [f,g,e]
    linarith only [h]
  have hs := Finset.sum_le_sum (s := univ) (fun i _ => Finset.sum_le_sum (s := univ)
    (fun j _ => Finset.sum_le_sum (s := univ) (fun k _ => point i j k)))
  rw [rotation f, rotation g] at hs
  have hf : score c x w = ∑ i, ∑ j, ∑ k, f i j k := by
    unfold score
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    by_cases h : Win c x i j k <;> simp [f,indicator,h]
  let p := push e w
  have hp := mass_push e hw
  have hsum : p 0 + p 1 + p 2 = 1 := by simpa [Fin.sum_univ_three,add_assoc] using hp.2
  have hg : (∑ i, ∑ j, ∑ k, g i j k) =
      ∑ a : Fin 3, p a * ∑ b : Fin 3, p b * ∑ d : Fin 3, p d * charge a b d := by
    simp only [p]
    simp_rw [pushed e w]
    simp only [Finset.mul_sum,g,mul_assoc]
  have endp := poly_quarter (p 0) (p 1) (hp.1 _) (hp.1 _)
  have heval : (∑ a : Fin 3, p a * ∑ b : Fin 3, p b * ∑ d : Fin 3, p d * charge a b d) =
      (p 0)^2*(1-p 0) + p 0*((1-p 0)^2-(p 1)^2) + (p 1)^2*(1-p 0 -p 1) := by
    simp only [Fin.sum_univ_three]
    generalize hp0 : p 0 = t at *
    generalize hp1 : p 1 = u at *
    generalize hp2 : p 2 = v at *
    norm_num [charge, Fin.ext_iff]
    have hv : v=1-t-u := by linarith
    rw [hv]; ring
  rw [hf]
  linarith only [hs, hg, heval, endp]

theorem beta_le_quarter {c : ℝ} (hc : 1 < c) (hφ : c*c < c+1) : beta c ≤ 1/4 := by
  apply csSup_le (values_nonempty hc)
  rintro b ⟨n,x,w,hx,hw,rfl⟩
  exact score_le_quarter hc hφ hx hw

#print axioms beta_le_quarter

end OneScale
