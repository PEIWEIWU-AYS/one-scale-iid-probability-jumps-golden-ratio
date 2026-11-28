import EndpointAsymptotics.PatternCounts
import EndpointAsymptotics.NormalizedPattern
import FiniteProfile
import OneScaleLaw

open Set Filter Finset IidJumpSpectra
open scoped BigOperators Topology
noncomputable section
namespace ClosedSpectrum

/-- A bound for adjoining a positive finite block of unit-weight labels above
`l` lower labels. All comparisons here are made at the single coefficient c. -/
def CountCap (c U : ℝ) : Prop :=
  ∀ (N : ℕ) (T : Finset (Fin N)) (x : Fin N → ℝ), T.Nonempty →
    (∀ i ∈ T, 0<x i) → ∀ l : ℕ,
    triples T (fun i j k => x i+x j≤c*x k) +
      2*(l:ℝ)*pairs T (fun i k => x i≤c*x k) + (l:ℝ)^2*(T.card:ℝ) ≤
        U*(((l:ℝ)+(T.card:ℝ))^3-(l:ℝ)^3)

/-- Extract successive positive scales of a right-realizable pattern. -/
theorem count_bound_of_cap {N : ℕ} {c U : ℝ} (cap : CountCap c U)
    (H : Fin N → Fin N → Fin N → Prop)
    (hf : ∀ d>c, ∃ x : Fin N → ℝ, (∀ i, 0<x i) ∧
      ∀ i j k, H i j k → x i+x j<d*x k) (s : Finset (Fin N)) :
    triples s H ≤ U*(s.card:ℝ)^3 := by
  classical
  induction s using Finset.strongInductionOn
  rename_i s ih
  
  by_cases hs : s.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp [triples_eq]
  letI : Nonempty (↥s) := ⟨⟨hs.choose,hs.choose_spec⟩⟩
  obtain ⟨y,hy,hpos,hwin⟩ := normalized_pattern
    (fun i j k : s => H i j k) c (fun d hd => by
      obtain ⟨x,hx,hw⟩ := hf d hd
      exact ⟨fun i => x i,fun i => hx i,fun i j k => hw i j k⟩)
  let u (i : Fin N) := if hi : i ∈ s then y ⟨i,hi⟩ else 0
  have uy (i) (hi : i∈s) : u i=y ⟨i,hi⟩ := dif_pos hi
  have hu (i) (hi : i∈s) : 0≤u i := (uy i hi).symm ▸ hy _
  have weak (i) (hi : i∈s) (j) (hj : j∈s) (k) (hk : k∈s) (h : H i j k) :
      u i+u j≤c*u k := by
    rw [uy _ hi,uy _ hj,uy _ hk]
    exact hwin _ _ _ h
  let L := zeros s u
  let T := positive s u
  obtain ⟨a,ha⟩ := hpos
  have ha' : 0<u a := (uy a a.property).symm ▸ ha
  have hT : T.Nonempty := ⟨a,Finset.mem_filter.mpr ⟨a.property,ha'⟩⟩
  have hLsub : L ⊂ s := by
    refine Finset.ssubset_iff_of_subset (Finset.filter_subset ..) |>.2 ⟨(a:Fin N),a.property,?_⟩
    exact fun r => ha'.ne' (Finset.mem_filter.mp r).2
  have ind := ih L hLsub
  have coeff := cap N T u hT (fun _ h => (Finset.mem_filter.mp h).2) L.card
  have hparts := partition_count_bound s u c H hu weak
  have hdis : Disjoint L T := by
    apply Finset.disjoint_left.mpr
    intro i h₁ h₂
    exact (Finset.mem_filter.mp h₂).2.ne' (Finset.mem_filter.mp h₁).2
  have hun : L∪T=s := by
    ext i
    simp only [L,T,zeros,positive,Finset.mem_union,Finset.mem_filter]
    constructor
    · exact fun h => h.elim And.left And.left
    · intro hi
      by_cases hz : u i=0
      · exact Or.inl ⟨hi,hz⟩
      · exact Or.inr ⟨hi,lt_of_le_of_ne (hu i hi) (Ne.symm hz)⟩
  have eqn := Finset.card_union_of_disjoint hdis
  rw [hun] at eqn
  have eqr : (s.card:ℝ)=(L.card:ℝ)+(T.card:ℝ) := by exact_mod_cast eqn
  rw [eqr]
  change triples s H ≤ triples L H + triples T _ + 2*(L.card:ℝ)*pairs T _ + (L.card:ℝ)^2*(T.card:ℝ) at hparts
  linarith only [hparts,ind,coeff]

private def comparisonTriple (N : ℕ) : Comparison 2 N ≃ (Fin N × Fin N × Fin N) :=
  (Equiv.prodCongr (finTwoArrowEquiv _) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

private def asTriple {N : ℕ} (A : Finset (Comparison 2 N)) (i j k : Fin N) : Prop :=
  (comparisonTriple N).symm (i,j,k) ∈ A

private theorem triple_card {N : ℕ} (A : Finset (Comparison 2 N)) :
    triples Finset.univ (asTriple A) = (A.card:ℝ) := by
  classical
  let f (q : Fin N × Fin N × Fin N) := if (comparisonTriple N).symm q ∈ A then (1:ℝ) else 0
  calc
    _ = ∑ q, f q := by
      rw [triples_eq]
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      by_cases h : asTriple A i j k <;> simp_all [f,asTriple]
    _ = ∑ q : Comparison 2 N, f (comparisonTriple N q) := (Equiv.sum_comp _ _).symm
    _ = _ := by simp [f]

private theorem feasible_triples {N : ℕ} {c : ℝ} {A : Finset (Comparison 2 N)}
    (h : ∀ d>c, PatternFeasible A d) :
    ∀ d>c, ∃ x : Fin N → ℝ, (∀ i, 0<x i) ∧
      ∀ i j k, asTriple A i j k → x i+x j<d*x k := by
  intro d hd
  obtain ⟨x,hx,hw⟩ := h d hd
  refine ⟨x,hx,fun i j k hA => ?_⟩
  have hh := hw ((comparisonTriple N).symm (i,j,k)) hA
  simpa [wins,comparisonTriple,Fin.sum_univ_two,finTwoArrowEquiv] using hh

/-- If every finite positive block obeys the bound, the right limit of the
unrestricted profile cannot exceed it. -/
theorem right_upper_of_countCap {c U v : ℝ} (cap : CountCap c U)
    (h : ∀ d>c, v≤extremal 2 d) : v≤U := by
  by_contra! hv
  have he := (survival_tendsto 3).eventually_const_lt (show U+1-v<1 by linarith)
  obtain ⟨N,hN,hgood⟩ := ((eventually_ge_atTop 1).and he).exists
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨A,ha,hfe⟩ := finite_pattern_persistence
    (fun A : Finset (Comparison 2 N) => U<frequency A) PatternFeasible c
    (fun _ _ _ hh => pattern_mono hh) (fun d hd => by
      obtain ⟨x,hx,hw⟩ := exists_sample_above (m:=2) (N:=N) (b:=U) (c:=d)
        (by linarith [h d hd])
      exact ⟨winsSet x d,hw,winsSet_feasible x hx d⟩)
  have bound := count_bound_of_cap cap (asTriple A) (feasible_triples hfe) univ
  rw [triple_card] at bound
  simp only [Finset.card_univ,Fintype.card_fin] at bound
  have hn : 0<(N:ℝ)^3 := by positivity
  have hh := (lt_div_iff₀ hn).1 (show U<(A.card:ℝ)/(N:ℝ)^3 from ha)
  linarith

#print axioms right_upper_of_countCap
end ClosedSpectrum
