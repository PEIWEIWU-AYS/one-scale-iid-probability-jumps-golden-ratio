import OneScaleGolden
import OneScaleJumps

open Filter MeasureTheory Set
open scoped Topology BigOperators NNReal ENNReal
open IidJumpSpectra
noncomputable section

namespace OneScale

/-- Every subcritical coefficient has a strict gap from one quarter. -/
theorem beta_lt_quarter {c : ℝ} (hc : 1 < c) (hφ : c < golden) : beta c < 1/4 := by
  obtain ⟨b,hb,hbφ,J,hJ,hjump⟩ := cofinal_jumps hφ
  have hcb : c < b := (le_max_left ..).trans_lt hb
  have h := hjump golden hbφ
  rw [beta_golden] at h
  linarith [beta_mono hc hcb.le]

private theorem choose_stretch {u : ℝ} (hu : u < golden) :
    ∃ K d : ℝ, 1 < K ∧ 1 < d ∧ d < golden ∧ 1 + K*(u-1) < d ∧
      (golden-d)*(1+K*(u-1)) < (K-1)*(2-golden) := by
  have hφ2 : golden < 2 := by
    dsimp [golden]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  have stretch : ContinuousAt (fun K : ℝ => 1+K*(u-1)) 1 := by fun_prop
  have e : ∀ᶠ K : ℝ in 𝓝 1, 1+K*(u-1) < golden :=
    stretch.tendsto.eventually_lt_const (by change 1+1*(u-1)<golden; linarith)
  have hr : ∀ᶠ K : ℝ in 𝓝[>] 1, 1 < K := self_mem_nhdsWithin
  obtain ⟨K,hK,hU⟩ := (hr.and (e.filter_mono nhdsWithin_le_nhds)).exists
  have gain : 0 < (K-1)*(2-golden) := mul_pos (by linarith) (by linarith)
  have loss : ContinuousAt (fun d : ℝ => (golden-d)*(1+K*(u-1))) golden := by fun_prop
  have near : ∀ᶠ d : ℝ in 𝓝 golden, (golden-d)*(1+K*(u-1)) < (K-1)*(2-golden) :=
    loss.tendsto.eventually_lt_const (by simpa using gain)
  have left : ∀ᶠ d : ℝ in 𝓝[<] golden, d < golden := self_mem_nhdsWithin
  obtain ⟨d,hd,h1,hUd,hgain⟩ := (left.and (((eventually_gt_nhds one_lt_golden).and
    ((eventually_gt_nhds hU).and near)).filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨K,d,hK,h1,hd,hUd,hgain⟩

/-- A fixed bound on the support ratio yields a uniform strict probability gap
at the golden ratio, also for measures with nonatomic components. -/
theorem golden_gap_on_fixed_support {u : ℝ} (hu : u < golden) :
    ∃ B < (1/4 : ℝ), ∀ (μ : Measure ℝ≥0) [IsProbabilityMeasure μ],
      (∀ᵐ x : ℝ≥0 ∂μ, 1 ≤ (x:ℝ) ∧ (x:ℝ) ≤ u) → iidWin 2 golden μ ≤ B := by
  obtain ⟨K,d,hK,hd,hdφ,hUd,hgain⟩ := choose_stretch hu
  refine ⟨beta d,beta_lt_quarter hd hdφ,?_⟩
  intro μ _ hs
  let U : ℝ := 1+K*(u-1)
  let g (x : ℝ≥0) : ℝ≥0 := ⟨max 0 (1+K*((x:ℝ)-1)),le_max_left ..⟩
  have hgm : Measurable g := by
    apply Measurable.subtype_mk
    fun_prop
  let ν := μ.map g
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hgm.aemeasurable
  have heq {x : ℝ≥0} (hx : 1 ≤ (x:ℝ)) : (g x : ℝ) = 1+K*((x:ℝ)-1) := by
    dsimp [g]
    exact max_eq_right (by nlinarith [mul_nonneg (show 0 ≤ K by linarith) (sub_nonneg.mpr hx)])
  have hb {x : ℝ≥0} (hx : 1 ≤ (x:ℝ) ∧ (x:ℝ) ≤ u) : 1 ≤ (g x:ℝ) ∧ (g x:ℝ) ≤ U := by
    rw [heq hx.1]
    dsimp [U]
    constructor
    · nlinarith [mul_nonneg (show 0 ≤ K by linarith) (sub_nonneg.mpr hx.1)]
    · nlinarith [mul_le_mul_of_nonneg_left hx.2 (show 0 ≤ K by linarith)]
  have hν : ∀ᵐ x : ℝ≥0 ∂ν, 1 ≤ (x:ℝ) ∧ (x:ℝ) ≤ U := by
    apply (ae_map_iff hgm.aemeasurable ?_).mpr
    · exact hs.mono fun _ h => hb h
    · exact (measurableSet_le measurable_const measurable_subtype_coe).inter
        (measurableSet_le measurable_subtype_coe measurable_const)
  let G (v : Fin 3 → ℝ≥0) (i : Fin 3) := g (v i)
  have hP : MeasurePreserving G (Measure.pi (fun _ : Fin 3 => μ)) (Measure.pi (fun _ : Fin 3 => ν)) :=
    measurePreserving_pi _ _ (fun _ => (⟨hgm,rfl⟩ : MeasurePreserving g μ ν))
  suffices hle : iidWin 2 golden μ ≤ iidWin 2 d ν from hle.trans (iid_le_beta_on_support hUd ν hν)
  have hall : ∀ᵐ v ∂(Measure.pi (fun _ : Fin 3 => μ)), ∀ i, 1 ≤ (v i : ℝ) ∧ (v i : ℝ) ≤ u :=
    eventually_all.mpr (fun i =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 3 => μ) (i := i)).eventually
        (p := fun z : ℝ≥0 => 1 ≤ (z:ℝ) ∧ (z:ℝ) ≤ u) hs)
  have hsubset : (winEvent 2 golden : Set (Fin 3 → ℝ≥0)) ≤ᵐ[Measure.pi (fun _ : Fin 3 => μ)]
      G ⁻¹' winEvent 2 d := by
    filter_upwards [hall] with v hv
    intro win
    change (∑ i : Fin 2, (v i.succ : ℝ)) < golden * (v 0 : ℝ) at win
    simp only [Fin.sum_univ_two] at win
    change (∑ i : Fin 2, (g (v i.succ) : ℝ)) < d*(g (v 0):ℝ)
    simp only [Fin.sum_univ_two]
    have h := mul_lt_mul_of_pos_left win (show 0 < K by linarith)
    have target := mul_le_mul_of_nonneg_left (hb (hv 0)).2 (sub_nonneg.mpr hdφ.le)
    change (golden-d)*(g (v 0):ℝ) ≤ (golden-d)*(1+K*(u-1)) at target
    rw [heq (hv 0).1] at target
    simp only [heq (hv _).1]
    nlinarith
  unfold iidWin
  rw [← hP.measure_preimage (measurableSet_winEvent 2 d).nullMeasurableSet]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)

/-- The genuine Borel one-scale supremum 1/4 has no maximizing law at φ. -/
theorem original_golden_nonattainment : (1/4 : ℝ) ∉ OriginalLawValues golden := by
  rw [← lawValues_eq_original]
  rintro ⟨μ,hμ,⟨u,hu,hs⟩,hscore⟩
  letI := hμ
  obtain ⟨B,hB,hl⟩ := golden_gap_on_fixed_support hu
  linarith [hl μ hs]

#print axioms golden_gap_on_fixed_support
#print axioms original_golden_nonattainment
end OneScale
