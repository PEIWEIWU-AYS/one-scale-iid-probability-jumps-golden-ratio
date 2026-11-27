import OneScaleJumpSize

open Set
namespace OneScale
noncomputable section

private theorem rank_one (w : Fin 1 → ℝ) : rankScore w = 0 := by
  norm_num [rankScore,RankWin,advance,Fin.sum_univ_succ]

private theorem rank_two (w : Fin 2 → ℝ) : rankScore w = w 0^2*w 1 := by
  norm_num [rankScore,RankWin,advance,Fin.sum_univ_succ]; ring_nf; simp

private theorem rank_three (w : Fin 3 → ℝ) :
    rankScore w = w 0^2*(w 1+w 2) + 2*w 0*w 1*w 2 := by
  norm_num [rankScore,RankWin,advance,Fin.sum_univ_succ]; ring

private theorem upper2 {w : Fin 2 → ℝ} (hw : Mass w) : rankScore w ≤ 4/27 := by
  have hsum := hw.2
  rw [Fin.sum_univ_two] at hsum
  rw [rank_two,show w 1=1-w 0 by linarith]
  nlinarith only [mul_nonneg (sq_nonneg (w 0-2/3)) (show 0≤w 0+1/3 by linarith [hw.1 0])]

private theorem upper3 {w : Fin 3 → ℝ} (hw : Mass w) : rankScore w ≤ 1/5 := by
  have hsum := hw.2
  rw [Fin.sum_univ_three] at hsum
  have h12 : w 1+w 2=1-w 0 := by linarith
  have hpop : 4*w 1*w 2≤(1-w 0)^2 := by rw [← h12]; nlinarith [sq_nonneg (w 1-w 2)]
  have hhalf : rankScore w ≤ (w 0-(w 0)^3)/2 := by
    rw [rank_three,h12]
    nlinarith only [mul_nonneg (hw.1 0) (sub_nonneg.mpr hpop)]
  apply hhalf.trans
  by_cases h : w 0≤2/5
  · nlinarith [pow_nonneg (hw.1 0) 3]
  · nlinarith only [h,mul_nonneg (sq_nonneg (w 0-3/5))
      (show 0≤w 0+6/5 by linarith [hw.1 0])]

/-- The first three new ranks give strict improvements. -/
theorem early_rank_strict {N : ℕ} (hn : 0<N) (hn' : N≤3) :
    rankMaximum N < rankMaximum (N+1) := by
  have dom {n : ℕ} (h : 0<n) (w : Fin n → ℝ) (hw : Mass w) :
      rankScore w ≤ rankMaximum n := (rankMaximum_attained h).2 ⟨w,hw,rfl⟩
  interval_cases N
  · obtain ⟨w,_,he⟩ := (rankMaximum_attained (show 0<1 by decide)).1
    have ha := rank_one w
    let v : Fin 2 → ℝ := ![2/3,1/3]
    have hv : Mass v := ⟨by intro i; fin_cases i <;> norm_num [v],by norm_num [v,Fin.sum_univ_two]⟩
    have h := dom (by decide) v hv
    rw [rank_two] at h
    norm_num [v] at h
    linarith
  · obtain ⟨w,hw,he⟩ := (rankMaximum_attained (show 0<2 by decide)).1
    let v : Fin 3 → ℝ := ![1/2,1/4,1/4]
    have hv : Mass v := ⟨by intro i; fin_cases i <;> norm_num [v],by rw [Fin.sum_univ_three]; change (1/2:ℝ)+1/4+1/4=1; norm_num⟩
    have h := dom (by decide) v hv
    rw [rank_three] at h
    change (1/2:ℝ)^2*(1/4+1/4)+2*(1/2)*(1/4)*(1/4) ≤ _ at h
    norm_num at h
    linarith [upper2 hw]
  · obtain ⟨w,hw,he⟩ := (rankMaximum_attained (show 0<3 by decide)).1
    let v : Fin 4 → ℝ := ![1/2,1/6,1/6,1/6]
    have hv : Mass v := ⟨by intro i; fin_cases i <;> norm_num [v],by norm_num [v,Fin.sum_univ_succ]⟩
    have h := dom (by decide) v hv
    norm_num [v,rankScore,RankWin,advance,Fin.sum_univ_succ] at h
    linarith [upper3 hw]

#print axioms early_rank_strict
end
end OneScale
