import EndpointAsymptotics.RankPopulationEndpoint

open Finset OneScale EndpointRecursion Filter
open scoped BigOperators
noncomputable section
namespace FullRankWindow

private theorem rank_rescale {k : ℕ} (p : ℝ) (w : Fin k → ℝ) :
    rankScore (fun i => p*w i) = p^3*rankScore w := by
  unfold rankScore
  rw [mul_sum]
  apply sum_congr rfl; intro i _
  rw [mul_sum]
  apply sum_congr rfl; intro j _
  rw [mul_sum]
  apply sum_congr rfl; intro k _
  split_ifs <;> ring

/-- Appending a bottom level preserves all earlier ranks and scales their
third moment by the cube of their retained mass. -/
private theorem extend_rank {k : ℕ} {p : ℝ} (hp : 0≤p) (hp1 : p≤1)
    (w : Fin k → ℝ) (hw : Mass w) :
    ∃ v : Fin (k+1) → ℝ, Mass v ∧ rankScore v=p-(1-rankScore w)*p^3 ∧
      (∑ i, v i ^ 3)=p^3*(∑ i, w i ^ 3)+(1-p)^3 := by
  let v : Fin (k+1) → ℝ := Fin.lastCases (1-p) (fun i => p*w i)
  have vl : v (Fin.last k)=1-p := by simp [v]
  have vc (i : Fin k) : v i.castSucc=p*w i := by simp [v]
  refine ⟨v,⟨?_,?_⟩,?_,?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => rw [vl];linarith
    | cast j => rw [vc];exact mul_nonneg hp (hw.1 _)
  · simp only [Fin.sum_univ_castSucc,vl,vc,←mul_sum,hw.2,mul_one];ring
  · rw [rank_remove_last]
    simp only [vl,vc,rank_rescale,←mul_sum,hw.2,mul_one]
    ring
  · simp only [Fin.sum_univ_castSucc,vc,vl,mul_pow,←mul_sum]

/-- Among the maximizers of the rank score there exists one whose cubed atom
masses control the partial sum of all previous optimal deficits. -/
theorem optimal_cube_mass (n : ℕ) :
    ∃ w : Fin (n+1) → ℝ, Mass w ∧ rankScore w=peak n ∧
      (x n)^2/8*(∑ j ∈ range (n+1), x j) ≤ ∑ i, w i^3 := by
  induction n with
  | zero =>
    refine ⟨fun _ => 1,⟨fun _ => zero_le_one,by simp⟩,by simp [rankScore,peak],?_⟩
    norm_num [x]
  | succ n ih =>
    obtain ⟨w,hw,score,ih⟩ := ih
    let s := Real.sqrt (1+x n)
    have xs := xpos n
    have s2 : s^2=1+x n := Real.sq_sqrt (by linarith)
    have spos : 0<s := Real.sqrt_pos.mpr (by linarith)
    have s1 : 1<s := by nlinarith only [s2,spos,xs]
    have plus' : 0<1+s := by linarith
    have xn : x (n+1)=2*x n/(s*(1+s)) := rfl
    have xn' : x (n+1)=2*(1-1/s) := by
      rw [xn]
      field_simp [spos.ne',plus'.ne']
      linear_combination -2*s*s2
    have px : 3*(1-peak n)=s^2 := by linarith only [s2,optimal_deficit n]
    have px' : peak (n+1)=2/(3*s) := by
      change 2/(3*Real.sqrt (3*(1-peak n)))=2/(3*s)
      rw [px,Real.sqrt_sq spos.le]
    have upd : 1/s-(1-peak n)*(1/s)^3=peak (n+1) := by
      rw [px'];field_simp [spos.ne'];linear_combination -s^2*px
    have coeff : 4/(s^2*(1+s)^2) ≤ 1/s^3 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [mul_nonneg (sq_nonneg s) (sq_nonneg (s-1))]
    have shrink : (x (n+1))^2 ≤ (1/s)^3*(x n)^2 := by
      calc
        _ = 4/(s^2*(1+s)^2)*(x n)^2 := by rw [xn];field_simp [spos.ne',plus'.ne'];ring
        _ ≤ (1/s^3)*(x n)^2 := mul_le_mul_of_nonneg_right coeff (sq_nonneg _)
        _ = _ := by ring
    have hsum : 0≤∑ j ∈ range (n+1), x j := sum_nonneg (fun i _ => (xpos i).le)
    obtain ⟨v,hv,vs,v3⟩ := extend_rank (one_div_pos.mpr spos).le
      ((div_le_iff₀ spos).2 (by linarith)) w hw
    refine ⟨v,hv,by rw [vs,score,upd],?_⟩
    rw [v3,sum_range_succ]
    have first := mul_le_mul_of_nonneg_right shrink hsum
    have prev := mul_le_mul_of_nonneg_left ih (show 0≤(1/s)^3 by positivity)
    have last : (x (n+1))^3=8*(1-1/s)^3 := by rw [xn'];ring
    nlinarith only [first,prev,last]

private theorem reciprocal_floor (n : ℕ) : 1/((n:ℝ)+1) ≤ x n := by
  have inv_le (k : ℕ) : (x k)⁻¹ ≤ (k:ℝ)+1 := by
    induction k with
    | zero => norm_num [x]
    | succ k ih =>
      have step := reciprocal_step k
      let s := Real.sqrt (1+x k)
      change (x (k+1))⁻¹-(x k)⁻¹=(s+2)/(2*(s+1)) at step
      have hs : 0≤s := Real.sqrt_nonneg _
      have bd : (s+2)/(2*(s+1)) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
      push_cast
      linarith only [ih,step,bd]
  have prod := mul_le_mul_of_nonneg_right (inv_le n) (xpos n).le
  rw [inv_mul_cancel₀ (xpos n).ne'] at prod
  exact (div_le_iff₀ (by positivity)).mpr (by linarith only [prod])

/-- A logarithmic lower bound for the partial sum of optimal deficits. -/
theorem log_le_sum_deficit (n : ℕ) : Real.log ((n:ℝ)+1) ≤ ∑ j ∈ range n, x j := by
  induction n with
  | zero => simp
  | succ n ih =>
    let t := (n:ℝ)+1
    have ht : 0<t := by dsimp [t];positivity
    have inc := Real.log_le_sub_one_of_pos (div_pos (show 0<t+1 by linarith) ht)
    rw [Real.log_div (by positivity) ht.ne'] at inc
    have id : (t+1)/t-1=1/t := by field_simp
    rw [id] at inc
    have w := reciprocal_floor n
    change 1/t ≤ x n at w
    rw [sum_range_succ,Nat.cast_succ]
    change Real.log (t+1) ≤ _
    change Real.log t ≤ _ at ih
    linarith only [ih,inc,w]

/-- The sum in the cube-mass bound diverges at least logarithmically. -/
theorem sum_deficit_atTop : Tendsto (fun n => ∑ j ∈ range (n+1), x j) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp b)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply le_trans _ (log_le_sum_deficit (n+1))
  rw [←Real.log_exp b]
  apply Real.log_le_log (Real.exp_pos b)
  have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  linarith only [hN,hn']

#print axioms optimal_cube_mass
#print axioms log_le_sum_deficit
#print axioms sum_deficit_atTop
end FullRankWindow
