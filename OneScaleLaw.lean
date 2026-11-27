import OneScaleModel
import CollisionLimit
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped BigOperators ENNReal NNReal Topology
open IidJumpSpectra
noncomputable section

namespace OneScale

/-- Borel probability laws supported between 1 and a fixed upper bound u<c. -/
def LawValues (c : ℝ) : Set ℝ := {p | ∃ μ : Measure ℝ≥0, IsProbabilityMeasure μ ∧
  (∃ u < c, ∀ᵐ x : ℝ≥0 ∂μ, 1 ≤ (x : ℝ) ∧ (x : ℝ) ≤ u) ∧ iidWin 2 c μ = p}

def lawBeta (c : ℝ) : ℝ := sSup (LawValues c)

private def tripleEquiv (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun f := (f 1, f 2, f 0)
  invFun p := ![p.2.2, p.1, p.2.1]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := by rfl


/-- A finite nonnegative weighted law realizes its triple score, with its
pushforward supported on the assigned atom values. -/
theorem weighted_law {α : Type*} [Fintype α] (c : ℝ) (x w : α → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hw : Mass w) :
    ∃ μ : Measure ℝ≥0, IsProbabilityMeasure μ ∧
      (∀ᵐ z : ℝ≥0 ∂μ, ∃ i, (z : ℝ) = x i) ∧ iidWin 2 c μ = score c x w := by
  classical
  let p : PMF α := PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw.1 i), hw.2]
    simp)
  let y (i : α) : ℝ≥0 := ⟨x i, hx i⟩
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSingletonClass α := ⟨fun _ => trivial⟩
  let μ := p.toMeasure.map y
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_map (measurable_of_countable y).aemeasurable
  refine ⟨μ,inferInstance,?_,?_⟩
  · apply (ae_map_iff (measurable_of_countable y).aemeasurable ?_).2
    · exact Eventually.of_forall fun i => ⟨i,rfl⟩
    · change MeasurableSet {z : ℝ≥0 | ∃ i : α, (z : ℝ) = x i}
      rw [show {z : ℝ≥0 | ∃ i : α, (z : ℝ) = x i} = ⋃ i : α, {z : ℝ≥0 | (z : ℝ) = x i} by ext; simp]
      exact MeasurableSet.iUnion fun i => measurableSet_eq_fun measurable_subtype_coe measurable_const
  let ν := Measure.pi (fun _ : Fin 3 => p.toMeasure)
  let xy (v : Fin 3 → α) (k : Fin 3) := y (v k)
  let A := xy ⁻¹' winEvent 2 c
  have hpush : MeasurePreserving y p.toMeasure μ := ⟨measurable_of_countable _,rfl⟩
  have hP : MeasurePreserving xy ν (Measure.pi (fun _ : Fin 3 => μ)) :=
    measurePreserving_pi _ _ (fun _ => hpush)
  have hxA : MeasurableSet A := (measurableSet_winEvent 2 c).preimage hP.measurable
  have hν (v : Fin 3 → α) : ν {v} = ∏ i, ENNReal.ofReal (w (v i)) := by
    change Measure.pi _ {v} = _
    rw [← Set.univ_pi_singleton, Measure.pi_pi]
    apply Finset.prod_congr rfl
    intro i _
    exact p.toMeasure_apply_singleton (v i) (measurableSet_singleton _)
  have hAt (v : Fin 3 → α) : v ∈ A ↔ Win c x (v 1) (v 2) (v 0) := by
    simp [A,xy,y,winEvent,Win,Fin.sum_univ_two]
  let f (q : α × α × α) :=
    if Win c x q.1 q.2.1 q.2.2 then w q.1 * w q.2.1 * w q.2.2 else 0
  have hwgt (v : Fin 3 → α) :
      (A.indicator (fun v => ν {v}) v).toReal = f (tripleEquiv α v) := by
    by_cases hv : v ∈ A
    · rw [Set.indicator_of_mem hv, hν]
      simp [f, tripleEquiv,hAt v |>.mp hv,Fin.prod_univ_succ,
        ENNReal.toReal_mul,ENNReal.toReal_ofReal (hw.1 _)]
      ring
    · rw [Set.indicator_of_not_mem hv]
      have hw0 : ¬ Win c x (v 1) (v 2) (v 0) := fun h => hv ((hAt v).2 h)
      simp [f,tripleEquiv,hw0]
  have hne (v : Fin 3 → α) : A.indicator (fun v => ν {v}) v ≠ ⊤ := by
    by_cases h : v ∈ A <;> simp [h,measure_ne_top,Set.indicator]
  rw [iidWin, ← hP.measure_preimage (measurableSet_winEvent 2 c).nullMeasurableSet]
  change (ν A).toReal = _
  rw [← ν.tsum_indicator_apply_singleton A hxA, tsum_fintype,
      ENNReal.toReal_sum (fun v _ => hne v)]
  simp_rw [hwgt]
  rw [Equiv.sum_comp (tripleEquiv α) f, Fintype.sum_prod_type]
  simp [f, score, Fintype.sum_prod_type]

/-- A finite weighted one-scale configuration gives an admissible Borel law. -/
theorem score_realized_by_law {c : ℝ} {n : ℕ} (x w : Fin n → ℝ)
    (hx : Cfg c x) (hw : Mass w) : score c x w ∈ LawValues c := by
  classical
  have hn : 0 < n := by
    by_contra! h
    obtain rfl : n = 0 := by omega
    simpa using hw.2
  letI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨μ,hμ,hs,he⟩ := weighted_law c x w (fun i => zero_le_one.trans (hx i).1) hw
  obtain ⟨a,_,ha⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  refine ⟨μ,hμ,⟨x a,(hx a).2,?_⟩,he⟩
  filter_upwards [hs] with z hz
  obtain ⟨i,hi⟩ := hz
  rw [hi]
  exact ⟨(hx i).1,ha i (Finset.mem_univ _)⟩

private theorem exists_sample_on_support (m N : ℕ) (c : ℝ) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (P : ℝ≥0 → Prop) (hP : ∀ᵐ z ∂μ, P z) :
    ∃ x : Fin N → ℝ≥0, (∀ i, P (x i)) ∧ ((goodComparisons m N).card : ℝ) * iidWin m c μ ≤
      ((winsSet (m := m) (fun i => (x i : ℝ)) c).card : ℝ) := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let select (q : Comparison m N) (x : Fin N → ℝ≥0) := x ∘ Fin.cons q.2 q.1
  let A (q : Comparison m N) := select q ⁻¹' winEvent m c
  let W (q : Comparison m N) := (A q).indicator (fun _ => (1:ℝ))
  let G := goodComparisons m N
  have meas (q : Comparison m N) : Measurable (select q) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hA q : MeasurableSet (A q) := (measurableSet_winEvent m c).preimage (meas q)
  have hint q : Integrable (W q) ν := (integrable_const (1:ℝ)).indicator (hA q)
  have freq (q) (hq : q ∈ G) : ∫ x, W q x ∂ν = iidWin m c μ := by
    have he : Injective (Fin.cons q.2 q.1) := (Finset.mem_filter.mp hq).2
    have hmap : ν.map (select q) = Measure.pi (fun _ : Fin (m+1) => μ) :=
      iid_map_injection μ _ he
    rw [iidWin, ← hmap, Measure.map_apply (meas q) (measurableSet_winEvent m c)]
    simpa [W, A, measureReal_def] using (integral_indicator_const (μ := ν) (1:ℝ) (hA q))
  have big : Integrable (fun x => ∑ q ∈ G, W q x) ν := integrable_finset_sum _ (fun q _ => hint q)
  have hall : ∀ᵐ x ∂ν, ∀ i, P (x i) :=
    Filter.eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae (i := i)).eventually hP)
  obtain ⟨x, hxgood, hx⟩ := exists_not_mem_null_integral_le big (ae_iff.mp hall)
  refine ⟨x, not_not.mp hxgood, ?_⟩
  have havg : ∫ x, (∑ q ∈ G, W q x) ∂ν = (G.card:ℝ) * iidWin m c μ := by
    rw [integral_finset_sum _ (fun q _ => hint q)]
    simp [Finset.sum_congr rfl freq]
  have sum_all : (∑ q : Comparison m N, W q x) =
      ((winsSet (m := m) (fun i => (x i : ℝ)) c).card : ℝ) := by
    have one (q : Comparison m N) : W q x =
        if wins (fun i => (x i : ℝ)) c q then 1 else 0 := by
      have hrel : x ∈ A q ↔ wins (fun i => (x i : ℝ)) c q := by
        simp [A, select, winEvent, wins, Function.comp_def]
      simp [W, Set.indicator_apply, hrel]
    simp_rw [one]
    simp [winsSet]
  rw [← sum_all, ← havg]
  apply hx.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro q _ _
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
theorem uniform_score {N : ℕ} (c : ℝ) (x : Fin N → ℝ) :
    score c x (fun _ => 1/(N : ℝ)) = frequency (winsSet (m := 2) x c) := by
  classical
  let f (q : Fin N × Fin N × Fin N) : ℝ := if Win c x q.1 q.2.1 q.2.2 then 1 else 0
  let eqv := (comparisonEquiv 2 N).trans (tripleEquiv (Fin N))
  have hr (q : Comparison 2 N) : (if wins x c q then (1:ℝ) else 0) = f (eqv q) := by
    simp [eqv,comparisonEquiv,tripleEquiv, f,Win,wins,Fin.consEquiv, Fin.sum_univ_two]
    rfl
  have hcard : ((winsSet (m := 2) x c).card : ℝ) = ∑ q : Fin N × Fin N × Fin N, f q := by
    calc
      _ = ∑ q : Comparison 2 N, if wins x c q then (1:ℝ) else 0 := by simp [winsSet]
      _ = _ := Fintype.sum_equiv eqv _ _ hr
  rw [frequency,hcard,Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type,Finset.sum_div,score]
  dsimp [f]
  congr 1
  ext i
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

private theorem values_subset_lawValues (c : ℝ) : values c ⊆ LawValues c := by
  rintro b ⟨n,x,w,hx,hw,rfl⟩
  exact score_realized_by_law x w hx hw

private lemma law_bdd (c : ℝ) : BddAbove (LawValues c) := by
  refine ⟨1, ?_⟩
  rintro b ⟨μ,hμ,_,rfl⟩
  exact iidWin_le_one _ _ _

private lemma values_nonempty {c : ℝ} (hc : 1 < c) : (values c).Nonempty := by
  let x : Fin 1 → ℝ := fun _ => 1
  let w : Fin 1 → ℝ := fun _ => 1
  exact ⟨_,1,x,w,fun _ => ⟨le_rfl,hc⟩,⟨fun _ => zero_le_one, by simp [w]⟩,rfl⟩

theorem iid_le_beta_on_support {c u : ℝ} (hu : u < c) (μ : Measure ℝ≥0)
    [IsProbabilityMeasure μ] (hs : ∀ᵐ z : ℝ≥0 ∂μ, 1 ≤ (z : ℝ) ∧ (z : ℝ) ≤ u) :
    iidWin 2 c μ ≤ beta c := by
  have ev : ∀ᶠ N : ℕ in atTop, survival 3 N * iidWin 2 c μ ≤ beta c := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    obtain ⟨x,hx,hscore⟩ := exists_sample_on_support 2 N c μ _ hs
    let z (i : Fin N) : ℝ := (x i : ℝ)
    let w (_ : Fin N) : ℝ := 1/(N:ℝ)
    have hcfg : Cfg c z := fun i => ⟨(hx i).1,(hx i).2.trans_lt hu⟩
    have hmass : Mass w := ⟨fun _ => by dsimp [w]; positivity, by simp [w,hN'.ne']⟩
    have hb : score c z w ≤ beta c :=
      le_csSup ((law_bdd c).mono (values_subset_lawValues c)) ⟨N,z,w,hcfg,hmass,rfl⟩
    rw [show score c z w = frequency (winsSet (m := 2) z c) from uniform_score c z] at hb
    refine le_trans ?_ hb
    rw [survival,frequency,div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity),
      ← goodComparisons_card 2 N]
    exact hscore
  apply le_of_tendsto_of_tendsto _ tendsto_const_nhds ev
  simpa using (survival_tendsto 3).mul (tendsto_const_nhds (x := iidWin 2 c μ))

/-- The supremum over finite weighted configurations equals the normalized
Borel one-scale problem, with strict support ratio. -/
theorem beta_eq_lawBeta {c : ℝ} (hc : 1 < c) : beta c = lawBeta c := by
  have hne := values_nonempty hc
  apply le_antisymm
  · exact csSup_le_csSup (law_bdd c) hne (values_subset_lawValues c)
  · apply csSup_le (hne.mono (values_subset_lawValues c))
    rintro b ⟨μ,hμ,⟨u,hu,hs⟩,rfl⟩
    exact iid_le_beta_on_support hu μ hs

/-- The win event is invariant under common positive scaling. -/
theorem iidWin_rescale (c : ℝ) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (d : ℝ≥0) (hd : 0 < d) :
    iidWin 2 c (μ.map (fun x => x / d)) = iidWin 2 c μ := by
  let g (x : ℝ≥0) := x / d
  have hg : Measurable g := by dsimp [g]; fun_prop
  let ν := μ.map g
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hg.aemeasurable
  let G (v : Fin 3 → ℝ≥0) (i : Fin 3) := g (v i)
  have hP : MeasurePreserving G (Measure.pi (fun _ : Fin 3 => μ))
      (Measure.pi (fun _ : Fin 3 => ν)) :=
    measurePreserving_pi _ _ (fun _ => (⟨hg,rfl⟩ : MeasurePreserving g μ ν))
  have hinv : G ⁻¹' winEvent 2 c = winEvent 2 c := by
    ext v
    change ((∑ i : Fin 2, (g (v i.succ) : ℝ)) < c * (g (v 0) : ℝ)) ↔ _
    dsimp [g]
    simp only [NNReal.coe_div, ← Finset.sum_div, ← mul_div_assoc]
    exact div_lt_div_iff_of_pos_right hd
  change ((Measure.pi (fun _ : Fin 3 => ν)) _).toReal = _
  rw [← hP.measure_preimage (measurableSet_winEvent 2 c).nullMeasurableSet,hinv]
  rfl

/-- Original one-scale normalization: support in [a,1], with c a>1. -/
def OriginalLawValues (c : ℝ) : Set ℝ := {p | ∃ μ : Measure ℝ≥0, IsProbabilityMeasure μ ∧
  (∃ a : ℝ, 0 < a ∧ 1 < c * a ∧ ∀ᵐ x : ℝ≥0 ∂μ, a ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1) ∧
    iidWin 2 c μ = p}

private lemma rescaled_support (μ : Measure ℝ≥0) (d : ℝ≥0) (hd : 0 < d)
    {a b : ℝ} (hab : ∀ᵐ x : ℝ≥0 ∂μ, a ≤ (x : ℝ) ∧ (x : ℝ) ≤ b) :
    ∀ᵐ x : ℝ≥0 ∂(μ.map (fun x => x/d)), a/(d:ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ b/(d:ℝ) := by
  have hg : Measurable (fun x : ℝ≥0 => x / d) := by fun_prop
  apply (ae_map_iff hg.aemeasurable ?_).2
  · filter_upwards [hab] with x hx
    exact ⟨div_le_div_of_nonneg_right hx.1 hd.le,div_le_div_of_nonneg_right hx.2 hd.le⟩
  · exact (measurableSet_le measurable_const measurable_subtype_coe).inter
          (measurableSet_le measurable_subtype_coe measurable_const)

theorem lawValues_eq_original (c : ℝ) : LawValues c = OriginalLawValues c := by
  apply Set.Subset.antisymm
  · rintro b ⟨μ,hμ,⟨u,huc,hu⟩,hscore⟩
    obtain ⟨x,hx⟩ := hu.exists
    have hu0 : 0 < u := by linarith [hx.1,hx.2]
    let d : ℝ≥0 := ⟨u,hu0.le⟩
    have hd : 0 < d := hu0
    have hg : Measurable (fun x : ℝ≥0 => x / d) := by fun_prop
    refine ⟨μ.map (fun x => x/d), isProbabilityMeasure_map hg.aemeasurable, ?_,
      (iidWin_rescale c μ d hd).trans hscore⟩
    refine ⟨1/u,by positivity,?_,?_⟩
    · rw [show c*(1/u)=c/u by ring,lt_div_iff₀ hu0]
      simpa using huc
    · simpa [d,hu0.ne'] using rescaled_support μ d hd hu
  · rintro b ⟨μ,hμ,⟨a,ha,hac,hs⟩,hscore⟩
    let d : ℝ≥0 := ⟨a,ha.le⟩
    have hd : 0 < d := ha
    have hg : Measurable (fun x : ℝ≥0 => x / d) := by fun_prop
    refine ⟨μ.map (fun x => x/d), isProbabilityMeasure_map hg.aemeasurable, ?_,
      (iidWin_rescale c μ d hd).trans hscore⟩
    refine ⟨1/a,(div_lt_iff₀ ha).2 hac,?_⟩
    simpa [d,ha.ne'] using rescaled_support μ d hd hs

/-- Equality with the Borel-law optimization in the original interval notation. -/
theorem beta_eq_original {c : ℝ} (hc : 1 < c) : beta c = sSup (OriginalLawValues c) := by
  rw [beta_eq_lawBeta hc,lawBeta,lawValues_eq_original]

#print axioms beta_eq_original
end OneScale
