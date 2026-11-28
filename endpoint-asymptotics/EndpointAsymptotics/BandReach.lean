import EndpointAsymptotics.EndpointCapSlack

open QuantitativeBands IidJumpSpectra

noncomputable section
namespace MultinacciBands

/-- Shortening the delay frees part of the square-root budget for extra bands. -/
private theorem reach_budget {m d j e : ℕ}
    (he : 8*e ≤ 7*d) (hj : 4*j^2 ≤ m*d) :
    Real.sqrt ((m:ℝ)+2+j) + 4*Real.sqrt e ≤
      Real.sqrt ((m:ℝ)+2) + 4*Real.sqrt d := by
  have D := Real.sq_sqrt (Nat.cast_nonneg d : 0 ≤ (d:ℝ))
  have M := Real.sq_sqrt (show 0 ≤ (m:ℝ)+2 by positivity)
  have hde : 8*(e:ℝ) ≤ 7*d := by exact_mod_cast he
  have cut : Real.sqrt e ≤ (15/16)*Real.sqrt d := by
    apply (Real.sqrt_le_left (by positivity)).2
    rw [mul_pow,D]
    nlinarith only [hde, (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hmd : 4*(j:ℝ)^2 ≤ (m:ℝ)*d := by exact_mod_cast hj
  have cross : 2*(j:ℝ) ≤ Real.sqrt ((m:ℝ)+2)*Real.sqrt d := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, M, D]
    nlinarith only [hmd, (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have more : Real.sqrt ((m:ℝ)+2+j) ≤
      Real.sqrt ((m:ℝ)+2) + Real.sqrt d / 4 := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith only [M, cross, sq_nonneg (Real.sqrt (d:ℝ))]
  linarith only [more,cut]

private theorem locate_root {m n : ℕ} {u : ℝ} (hm : 32 ≤ m) (hn : 0 < n)
    (size : 4*(m:ℝ) ≤ (3/2:ℝ)^n) (hu : 1 < u) (hu2 : u < 2)
    (root : (2-u)*u^n = 1) : 2-1/(2*(m:ℝ)) ≤ u ∧ u < 2-1/(2:ℝ)^n := by
  have hm' : (32:ℝ) ≤ m := by exact_mod_cast hm
  have hu0 : 0 < u := zero_lt_one.trans hu
  have half : (3/2:ℝ) ≤ u := by
    apply le_of_not_gt
    intro bad
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    change n=k+1 at hk
    have root' : (2-u)*u^(k+1)=1 := by simpa only [←hk] using root
    have small := FullRankWindow.threshold_opens_right hu bad root'
    rw [←hk] at small
    linarith only [small,size,hm']
  have hpow : 2*(m:ℝ) ≤ u^n :=
    (show 2*(m:ℝ) ≤ (3/2:ℝ)^n by linarith only [size,hm']).trans
      (pow_le_pow_left₀ (by norm_num) half n)
  have diff : 2-u = 1/u^n := (eq_div_iff (pow_pos hu0 n).ne').2 root
  have inv := one_div_le_one_div_of_le (show 0 < 2*(m:ℝ) by linarith only [hm']) hpow
  have strict := one_div_lt_one_div_of_lt (pow_pos hu0 n) (pow_lt_pow_left₀ hu2 hu0.le hn.ne')
  exact ⟨by linarith only [inv,diff], by linarith only [strict,diff]⟩

/-- A single bound strictly below the published cap covers all dyadic
endpoints through every index j with 4 j² ≤ m d. The integer d has logarithmic
size, as witnessed by the displayed lower and upper constraints. -/
theorem square_root_band_reach {m : ℕ} (hm : 32 ≤ m) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ m ∧ 4*(m:ℝ) ≤ (3/2:ℝ)^d ∧ (d:ℝ) < delayBudget m ∧
      ∃ B < 2/3 - 4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m))^2),
        B = intervalCap m ∧ ∀ j : ℕ, 4*j^2 ≤ m*d →
          let t := 2-1/(2:ℝ)^(m+j)
          ∃ (K e : ℕ) (r : ℝ), 0 < K ∧ 0 < e ∧ 1 < r ∧ r*(1+(r⁻¹)^e) ≤ 2-1/(2*(m:ℝ)) ∧
            r*(1+(r⁻¹)^e) ≤ t ∧
            (r⁻¹)^(K+e) ≤ 2-t ∧
            2/3-4/(9*(Real.sqrt (K:ℝ)+4*Real.sqrt (e:ℝ))^2) ≤ B ∧
            (∀ x : ℝ, x ≤ t → extremal 2 x ≤ B) ∧
            ∀ u : ℝ, 1 < u → u < 2 → (2-u)*u^(m+j) = 1 →
              r*(1+(r⁻¹)^e) ≤ u ∧ (r⁻¹)^(K+e) ≤ 2-u ∧ u < t := by
  obtain ⟨d,hd,dm,shift,hlog⟩ := choose_delay m hm
  let r : ℝ := 2-1/(m:ℝ)
  let e := (3*d+3)/4
  have hm' : (32:ℝ) ≤ m := by exact_mod_cast hm
  have mp : 0 < (m:ℝ) := by linarith only [hm']
  have d8 : 8 ≤ d := by
    by_contra! bad
    have small := pow_le_pow_right₀ (by norm_num : 1 ≤ (3/2:ℝ)) (show d ≤ 7 by omega)
    norm_num at small
    linarith only [hm',small,shift]
  have epos : 0 < e := by dsimp [e]; omega
  have eupper : 8*e ≤ 7*d := by dsimp [e]; omega
  have elower : 3*d ≤ 4*e := by dsimp [e]; omega
  have rlo : (7/4:ℝ) ≤ r := by
    have inv : 1/(m:ℝ) ≤ 1/4 := (div_le_iff₀ mp).2 (by linarith only [hm'])
    dsimp only [r]; linarith only [inv]
  have rp : 0 < r := (by norm_num : (0:ℝ) < 7/4).trans_le rlo
  have r1 : 1 < r := (by norm_num : (1:ℝ) < 7/4).trans_le rlo
  have r2 : r ≤ 2 := by dsimp only [r]; linarith only [one_div_pos.mpr mp]
  have power : (3/2:ℝ)^d ≤ r^e := by
    have cube : ((3/2:ℝ)^4) ≤ r^3 :=
      (by norm_num : (3/2:ℝ)^4 ≤ (7/4:ℝ)^3).trans (pow_le_pow_left₀ (by norm_num) rlo 3)
    have h := pow_le_pow_left₀ (by positivity) cube d
    rw [←pow_mul,←pow_mul] at h
    have h' := h.trans (pow_le_pow_right₀ r1.le elower)
    apply (pow_le_pow_iff_left₀ (by positivity) (pow_nonneg rp.le e) (by decide : (4:ℕ)≠0)).mp
    simpa only [←pow_mul,Nat.mul_comm] using h'
  have re : 4*(m:ℝ) ≤ r^e := shift.trans power
  have invre : (r⁻¹)^e ≤ 1/(4*(m:ℝ)) := by
    rw [inv_pow,←one_div]
    exact one_div_le_one_div_of_le (by positivity) re
  have gate : r*(1+(r⁻¹)^e) ≤ 2-1/(2*(m:ℝ)) := by
    have p := mul_le_mul_of_nonneg_left invre rp.le
    have q := mul_le_mul_of_nonneg_right r2 (show 0 ≤ 1/(4*(m:ℝ)) by positivity)
    have v : r + 2*(1/(4*(m:ℝ))) = 2-1/(2*(m:ℝ)) := by dsimp only [r]; field_simp; ring
    linarith only [p,q,v]
  have bern := one_add_mul_sub_le_pow (show -1 ≤ r/2 by linarith only [rlo]) m
  have id : 1+(m:ℝ)*(r/2-1)=1/2 := by dsimp only [r]; field_simp; ring
  rw [id] at bern
  have rb : r/2 ≤ 1 := (div_le_one (by norm_num : (0:ℝ)<2)).2 r2
  have half (n : ℕ) (hn : n ≤ m) : (2:ℝ)^n / 2 ≤ r^n := by
    have h := bern.trans (pow_le_pow_of_le_one (by positivity : 0 ≤ r/2) rb hn)
    rw [div_pow] at h
    have a := (le_div_iff₀ (by positivity : 0<(2:ℝ)^n)).mp h
    linarith only [a]
  have sqr : (2:ℝ) ≤ r^2 :=
    (by norm_num : (2:ℝ) ≤ (7/4:ℝ)^2).trans (pow_le_pow_left₀ (by norm_num) rlo 2)
  let B := 2/3 - 4/(9*(Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (d:ℝ))^2)
  refine ⟨d,hd,dm,shift,hlog,B,?_,?_,?_⟩
  · dsimp only [B]
    have lt : Real.sqrt (d:ℝ) < Real.sqrt (delayBudget m) := Real.sqrt_lt_sqrt (Nat.cast_nonneg d) hlog
    have h : Real.sqrt ((m:ℝ)+2)+4*Real.sqrt d <
        Real.sqrt ((m:ℝ)+2)+4*Real.sqrt (delayBudget m) := by linarith only [lt]
    apply sub_lt_sub_left
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ h (by positivity) (by decide : (2:ℕ)≠0)) (by norm_num)
  · dsimp only [B,intervalCap]
    rw [←delay_eq_canonical hm shift hlog]
  · intro j hj
    have jm : j ≤ m := by
      apply le_of_not_gt
      intro bad
      have large := Nat.mul_self_lt_mul_self bad
      have ub := Nat.mul_le_mul_left m dm
      nlinarith only [hj,large,ub]
    let n := m+j
    let K := m+2+j
    let t := 2-1/(2:ℝ)^n
    have npos : 0<(2:ℝ)^n := by positivity
    have gate' : r*(1+(r⁻¹)^e) ≤ t := by
      have large : 2*(m:ℝ) ≤ (2:ℝ)^n := by
        have h := shift.trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (3/2:ℝ)≤2) d)
        have H := h.trans (pow_le_pow_right₀ (by norm_num) (show d≤n by dsimp [n]; omega))
        linarith only [H,mp]
      exact gate.trans (sub_le_sub_left (one_div_le_one_div_of_le (by positivity) large) _)
    have fit : (r⁻¹)^(K+e) ≤ 2-t := by
      have mbase : (2:ℝ)^m ≤ r^m*r^2 := by
        have h := mul_le_mul_of_nonneg_left sqr (pow_nonneg rp.le m)
        linarith only [half m le_rfl,h]
      have jbase : (2:ℝ)^j ≤ r^j*r^e := by
        have h := mul_le_mul_of_nonneg_left (show (2:ℝ) ≤ r^e by linarith only [re,hm']) (pow_nonneg rp.le j)
        linarith only [half j jm,h]
      have bound := mul_le_mul mbase jbase (by positivity) (by positivity)
      have L : (2:ℝ)^n ≤ r^(K+e) := by
        dsimp [n,K]
        simpa only [pow_add,mul_assoc] using bound
      have value : 2-t=1/(2:ℝ)^n := by dsimp only [t]; ring
      rw [value,inv_pow,←one_div]
      exact one_div_le_one_div_of_le npos L
    have dep := population_band_upper K e epos r1 (by dsimp only [t]; linarith only [one_div_pos.mpr npos] : t<2) gate' fit
    have budget := reach_budget eupper hj
    have den : Real.sqrt (K:ℝ)+4*Real.sqrt e ≤ Real.sqrt ((m:ℝ)+2)+4*Real.sqrt d := by
      dsimp only [K]; push_cast; exact budget
    have better : 2/3-4/(9*(Real.sqrt (K:ℝ)+4*Real.sqrt (e:ℝ))^2) ≤ B := by
      dsimp only [B]
      apply sub_le_sub_left
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) den 2) (by norm_num)
    refine ⟨K,e,r,(by dsimp only [K]; omega),epos,r1,gate,gate',fit,better,
      fun x hx => ((extremal_mono 2 hx).trans dep).trans better, ?_⟩
    intro u hu hu2 root
    have size := shift.trans (pow_le_pow_right₀ (by norm_num : 1 ≤ (3/2:ℝ)) (show d≤m+j by omega))
    obtain ⟨left,right⟩ := locate_root hm (show 0 < m+j by omega) size hu hu2 root
    exact ⟨gate.trans left, fit.trans (sub_le_sub_left right.le 2), right⟩

#print axioms square_root_band_reach
end MultinacciBands
