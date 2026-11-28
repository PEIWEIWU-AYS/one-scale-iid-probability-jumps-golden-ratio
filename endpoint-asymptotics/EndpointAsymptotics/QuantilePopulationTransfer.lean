import EndpointAsymptotics.RankPopulationEndpoint
import CollisionLimit
open Finset OneScale IidJumpSpectra Filter
open scoped Topology BigOperators
noncomputable section
namespace QuantitativeBands

/-- Select a support point where the upper tail crosses the requested mass.
The two inequalities allow arbitrary atoms at the cut. -/
theorem finite_quantile {n : ℕ} (x w : Fin n → ℝ) (hx : ∀ i, 0<x i)
    (hw : Mass w) {ε : ℝ} (he : 0<ε) (he1 : ε≤1) :
    ∃ z : ℝ, 0<z ∧
      (∑ i ∈ univ.filter (fun i => z<x i), w i) ≤ ε ∧
      ε ≤ ∑ i ∈ univ.filter (fun i => z≤x i), w i := by
  classical
  have hn : n≠0 := by rintro rfl;simpa using hw.2
  letI : NeZero n := ⟨hn⟩
  let tail (t : ℝ) := ∑ i ∈ univ.filter (fun i => t≤x i), w i
  let good := univ.filter (fun i => ε≤tail (x i))
  obtain ⟨lo,_,least⟩ := exists_min_image univ x univ_nonempty
  have all : univ.filter (fun i => x lo≤x i)=univ := by
    ext i; simp [least i (mem_univ i)]
  have hlo : lo∈good := by simp [good,tail,all,hw.2,he1]
  obtain ⟨k,hk,maximal⟩ := exists_max_image good x ⟨lo,hlo⟩
  refine ⟨x k,hx k,?_,(mem_filter.mp hk).2⟩
  let above := univ.filter (fun i => x k < x i)
  by_cases ne : above.Nonempty
  · obtain ⟨j,hj,leastAbove⟩ := exists_min_image above x ne
    have lt := (mem_filter.mp hj).2
    have eq : above = univ.filter (fun i => x j≤x i) := by
      ext i
      constructor
      · intro hi; exact mem_filter.mpr ⟨mem_univ _,leastAbove i hi⟩
      · intro hi; exact mem_filter.mpr ⟨mem_univ _,lt.trans_le (mem_filter.mp hi).2⟩
    change (∑ i ∈ above, w i)≤ε
    rw [eq]
    by_contra! gt
    exact (not_le_of_gt lt) (maximal j (mem_filter.mpr ⟨mem_univ _,gt.le⟩))
  · change (∑ i ∈ above, w i) ≤ ε
    rw [not_nonempty_iff_eq_empty.mp ne,sum_empty]
    exact he.le

/-- A finite nonnegative configuration can be shifted into the positive
half-line without losing any of its strict wins. -/
private theorem positive_shift {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i,0≤x i) (c : ℝ) :
    ∃ y : Fin n → ℝ, (∀ i,0<y i) ∧
      ∀ i j k, Win c x i j k → Win c y i j k := by
  have preserve (i j k : Fin n) : ∀ᶠ t : ℝ in 𝓝 (0:ℝ),
      Win c x i j k → Win c (fun h => x h+t) i j k := by
    by_cases h : Win c x i j k
    · have co : Continuous (fun t : ℝ => c*(x k+t)-((x i+t)+(x j+t))) := by fun_prop
      have pos : 0 < c*(x k+0)-((x i+0)+(x j+0)) := by simpa [Win] using sub_pos.mpr h
      filter_upwards [co.continuousAt.tendsto.eventually_const_lt pos] with t ht
      intro _
      exact sub_pos.mp ht
    · exact Eventually.of_forall fun _ f => (h f).elim
  have ev : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), ∀ i j k, Win c x i j k → Win c (fun h => x h+t) i j k :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k => preserve i j k
  have gt : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t := self_mem_nhdsWithin
  obtain ⟨t,ht,h⟩ := (gt.and
    (ev.filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨fun i => x i+t,fun i => add_pos_of_nonneg_of_pos (hx i) ht,h⟩

theorem population_of_positive_cap {c U : ℝ}
    (cap : ∀ (N : ℕ) (y w : Fin N → ℝ), (∀ i,0<y i) → Mass w → score c y w ≤ U) :
    extremal 2 c ≤ U := by
  classical
  by_contra! bad
  have near := (survival_tendsto 3).eventually_const_lt (show U+1-extremal 2 c<1 by linarith)
  obtain ⟨N,hN,hS⟩ := ((eventually_ge_atTop 1).and near).exists
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨x,hx,high⟩ := exists_sample_above (m:=2) (N:=N) (c:=c) (b:=U) (by linarith)
  obtain ⟨y,hy,keeps⟩ := positive_shift x hx c
  let w (_ : Fin N) := 1/(N:ℝ)
  have hw : Mass w := ⟨fun _ => by dsimp [w]; positivity,by simp [w,NeZero.ne N]⟩
  have larger : score c x w ≤ score c y w := by
    unfold score
    apply sum_le_sum;intro i _
    apply sum_le_sum;intro j _
    apply sum_le_sum;intro k _
    split_ifs with h h' h'
    · exact le_rfl
    · exact False.elim (h' (keeps i j k h))
    · exact mul_nonneg (mul_nonneg (hw.1 i) (hw.1 j)) (hw.1 k)
    · exact le_rfl
  have eq := uniform_score (N:=N) c x
  rw [←eq] at high
  exact (not_le_of_gt high) (larger.trans (cap N y w hy hw))

#print axioms finite_quantile
#print axioms population_of_positive_cap
end QuantitativeBands
