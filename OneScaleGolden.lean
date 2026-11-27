import OneScaleLimit
import OneScaleLimitLower
import OneScaleLaw

open Filter Set
open scoped Topology BigOperators
noncomputable section

namespace OneScale

private theorem finite_persists_before {n : ℕ} {c : ℝ} (hc : 1 < c)
    {x w : Fin n → ℝ} (hx : Cfg c x) (hw : Mass w) :
    ∃ d, 1 < d ∧ d < c ∧ Cfg d x ∧ score c x w ≤ score d x w := by
  have ep (i j k : Fin n) : ∀ᶠ d in 𝓝 c, Win c x i j k → Win d x i j k := by
    by_cases h : Win c x i j k
    · have he : ContinuousAt (fun d : ℝ => d * x k) c := by fun_prop
      exact (he.tendsto.eventually_const_lt h).mono fun _ hh _ => hh
    · exact Eventually.of_forall fun _ hh => (h hh).elim
  have ev := Filter.eventually_all.mpr fun i =>
    Filter.eventually_all.mpr fun j => Filter.eventually_all.mpr (ep i j)
  have es : ∀ᶠ d in 𝓝 c, ∀ i, x i < d := Filter.eventually_all.mpr fun i => lt_mem_nhds (hx i).2
  have h1 : ∀ᶠ d in 𝓝 c, 1 < d := lt_mem_nhds hc
  have hL : ∀ᶠ d in 𝓝[<] c, d < c := self_mem_nhdsWithin
  obtain ⟨d,hd,h1,hs,hwin⟩ := (hL.and ((h1.and (es.and ev)).filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨d,h1,hd, fun i => ⟨(hx i).1,hs i⟩,score_mono_wins hw hwin⟩

private theorem golden_value_of_upper
    (upper : ∀ {c : ℝ}, 1 < c → c*c < c+1 → beta c ≤ 1/4) : beta golden = 1/4 := by
  apply le_antisymm
  · apply csSup_le (values_nonempty one_lt_golden)
    rintro b ⟨n,x,w,hx,hw,rfl⟩
    obtain ⟨d,h1,hd,hs,hle⟩ := finite_persists_before one_lt_golden hx hw
    have hv : score d x w ≤ beta d := le_csSup (bdd_values d) ⟨n,x,w,hs,hw,rfl⟩
    exact hle.trans (hv.trans (upper h1 ((before_golden h1).mp hd)))
  · by_contra! h
    have hl := eventually_above_below_quarter h
    have es : ∀ᶠ d in 𝓝[<] golden, 1 < d := (lt_mem_nhds one_lt_golden).filter_mono nhdsWithin_le_nhds
    have et : ∀ᶠ d in 𝓝[<] golden, d < golden := self_mem_nhdsWithin
    obtain ⟨d,hgt,hs,ht⟩ := (hl.and (es.and et)).exists
    exact (not_lt_of_ge (beta_mono hs ht.le)) hgt

private theorem golden_limit_of_upper
    (upper : ∀ {c : ℝ}, 1 < c → c*c < c+1 → beta c ≤ 1/4) :
    Tendsto beta (𝓝[<] golden) (𝓝 (1/4)) := by
  apply tendsto_order.2
  refine ⟨fun b hb => eventually_above_below_quarter hb, ?_⟩
  intro b hb
  have es : ∀ᶠ d in 𝓝[<] golden, 1 < d := (lt_mem_nhds one_lt_golden).filter_mono nhdsWithin_le_nhds
  have et : ∀ᶠ d in 𝓝[<] golden, d < golden := self_mem_nhdsWithin
  filter_upwards [es,et] with d h1 hd
  exact (upper h1 ((before_golden h1).mp hd)).trans_lt hb

/-- Two equally weighted atoms already certify a fixed improvement to the
right of the golden ratio, as in Zaytsev and Bellec, Corollary 6.2(4). -/
theorem three_eighths_right {c : ℝ} (hc : golden < c) : 3/8 ≤ beta c := by
  classical
  have h1 := one_lt_golden.trans hc
  have hd : 0 < c-1 := sub_pos.mpr h1
  have hphi : golden*golden = golden+1 := by
    dsimp [golden]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  have hgg : 1/(c-1) < c := by
    apply (div_lt_iff₀ hd).2
    nlinarith [mul_pos (sub_pos.mpr hc) (show 0<c+golden-1 by linarith [one_lt_golden])]
  obtain ⟨T,hT,hTc⟩ := exists_between (max_lt h1 hgg)
  have hT1 : 1 < T := (le_max_left ..).trans_lt hT
  have hT' := (div_lt_iff₀ hd).1 ((le_max_right ..).trans_lt hT)
  let x : Fin 2 → ℝ := ![1,T]
  let w (_ : Fin 2) := (1/2:ℝ)
  have hx : Cfg c x := by
    intro k
    fin_cases k
    · exact ⟨le_rfl,h1⟩
    · exact ⟨hT1.le,hTc⟩
  have hw : Mass w := ⟨by intro; norm_num [w],by norm_num [w,Fin.sum_univ_two]⟩
  have hh : score c x w ≤ beta c := le_csSup (bdd_values c) ⟨2,x,w,hx,hw,rfl⟩
  apply le_trans ?_ hh
  have h11 : (1:ℝ)+1 < c*T := by nlinarith
  have h1T : 1+T < c*T := by nlinarith
  have hT1' : T+1 < c*T := by linarith
  simp [score,Win,x,w,Fin.sum_univ_two,h11,h1T,hT1']
  split_ifs <;> norm_num

theorem beta_golden : beta golden = 1/4 := golden_value_of_upper @beta_le_quarter

theorem beta_tendsto_golden : Tendsto beta (𝓝[<] golden) (𝓝 (1/4)) :=
  golden_limit_of_upper @beta_le_quarter

theorem original_golden_value : sSup (OriginalLawValues golden) = 1/4 := by
  rw [← beta_eq_original one_lt_golden, beta_golden]

theorem original_tendsto_golden :
    Tendsto (fun c => sSup (OriginalLawValues c)) (𝓝[<] golden) (𝓝 (1/4)) := by
  apply beta_tendsto_golden.congr'
  have es : ∀ᶠ c in 𝓝[<] golden, 1 < c := (lt_mem_nhds one_lt_golden).filter_mono nhdsWithin_le_nhds
  exact es.mono fun _ hc => beta_eq_original hc

theorem original_golden_jump :
    IidJumpSpectra.RightJump (fun c => sSup (OriginalLawValues c)) golden (1/8) := by
  intro t ht
  change sSup (OriginalLawValues golden) + 1/8 ≤ sSup (OriginalLawValues t)
  rw [original_golden_value, ← beta_eq_original (one_lt_golden.trans ht)]
  linarith [three_eighths_right ht]

#print axioms original_golden_value
#print axioms original_tendsto_golden
#print axioms original_golden_jump
end OneScale
