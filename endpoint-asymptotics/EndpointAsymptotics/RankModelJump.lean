import EndpointAsymptotics.RankUniformGap
import EndpointAsymptotics.RankThresholdMonotone

open OneScale ClosedSpectrum Set
noncomputable section
namespace FullRankWindow

/-- Strict finite-block model with at most n+1 positive values, arbitrary
weights and the compactified lower-scale mass parameter. -/
def finiteBlockValues (n : ℕ) (c : ℝ) : Set ℝ :=
  {v | ∃ (P : RankTables (n+1)), strictFeasible c P ∧
    ∃ (w : Fin (n+1) → ℝ), Mass w ∧ ∃ p∈Set.Icc (0:ℝ) 1,
    v=mixScore (tableTriple P w) (tablePair P w) p}

def finiteBlockProfile (n : ℕ) (c : ℝ) : ℝ := sSup (finiteBlockValues n c)

private theorem nonempty_values (n : ℕ) {c : ℝ} (hc : 1<c) (h2 : c<2) :
    (finiteBlockValues n c).Nonempty := by
  let P : RankTables (n+1) := (fun _ _ _ => false,fun _ _ => true)
  have f : strictFeasible c P := by
    refine ⟨fun _ => 1,rfl,fun _ _ => zero_lt_one,fun _ _ _ _ _ => le_rfl,?_,?_⟩
    · intro i j k
      simp only [P,Bool.false_eq_true,mul_one,false_iff]
      linarith
    · intro i k
      simp [P,hc]
  obtain ⟨w,hw,_⟩ := (rank_peak n).1
  exact ⟨_,P,f,w,hw,0,⟨le_rfl,zero_le_one⟩,rfl⟩

private theorem values_bdd (n : ℕ) {c : ℝ} (h2 : c<2) : BddAbove (finiteBlockValues n c) := by
  refine ⟨1,?_⟩
  rintro _ ⟨P,fe,w,hw,p,hp,rfl⟩
  have bounds := table_caps h2 fe w hw
  have hB : tableTriple P w≤1 := bounds.1.trans (((rank_peak n).2 w hw).trans (by linarith only [peak_lt (n:=n)]))
  have hQ := bounds.2
  have coef : 0≤2*p*(1-p) := mul_nonneg (mul_nonneg (by norm_num) hp.1) (sub_nonneg.mpr hp.2)
  unfold mixScore
  apply (div_le_iff₀ (by nlinarith only [sq_nonneg (p+1/2)])).2
  nlinarith only [mul_le_mul_of_nonneg_left hB (sq_nonneg (1-p)),mul_le_mul_of_nonneg_left hQ coef,hp.1,sq_nonneg p]

private theorem right_mem {n : ℕ} {c : ℝ} (hc : 1<c) (h2 : c<2)
    (h : (2-c)*c^(n+1)<1) {p : ℝ} (hp : p∈Set.Icc (0:ℝ) 1) :
    mixScore (peak n) 1 p ∈ finiteBlockValues n c := by
  classical
  let P : RankTables (n+1) := (fun i j k => decide (k < i ∨ k < j),fun _ _ => true)
  obtain ⟨x,h0,hx,pair,tr⟩ := (strict_iff hc h2).2 h
  have fe : strictFeasible c P := by
    refine ⟨x,h0,hx,?_,?_,?_⟩
    · intro i hi j hj hij
      rcases eq_or_lt_of_le hij with rfl | less
      · exact le_rfl
      · have hwin := (tr j hj j hj i hi).2 (Or.inl less)
        nlinarith only [hwin,mul_pos (sub_pos.mpr h2) (hx i hi)]
    · intro i j k
      simpa only [P,decide_eq_true_eq] using
        (tr i.val (by omega) j.val (by omega) k.val (by omega)).symm
    · intro i k
      exact ⟨fun _ => pair i.val (by omega) k.val (by omega),fun _ => rfl⟩
  obtain ⟨w,hw,he⟩ := (rank_peak n).1
  refine ⟨P,fe,w,hw,p,hp,?_⟩
  have pscore : tableTriple P w=peak n := by simpa [tableTriple,P,rankScore] using he
  have qscore : tablePair P w=1 := by simp [tablePair,P,←Finset.mul_sum,hw.2]
  rw [pscore,qscore]

/-- Genuine jumps of the finite-block model. The same fixed positive gap
works for every coefficient to the right of the root and below two. -/
theorem finite_profile_jump {n : ℕ} {c : ℝ} (hc : 1<c) (h2 : c<2)
    (root : (2-c)*c^(n+1)=1) :
    ∃ g : ℝ, 0<g ∧ ∀ d : ℝ, c<d → d<2 →
      finiteBlockProfile n c+g≤finiteBlockProfile n d := by
  obtain ⟨q,hq,g,hg,all⟩ := strict_uniform_gap hc h2 root
  have upper : finiteBlockProfile n c≤mixScore (peak n) 1 q-g := by
    apply csSup_le (nonempty_values n hc h2)
    rintro _ ⟨P,hP,w,hw,p,hp,rfl⟩
    linarith only [all P hP w hw p hp]
  refine ⟨g,hg,fun d hd hd2 => ?_⟩
  have fill := right_mem (hc.trans hd) hd2 (threshold_opens_right hc hd root) hq
  have lower : mixScore (peak n) 1 q≤finiteBlockProfile n d := le_csSup (values_bdd n hd2) fill
  linarith only [upper,lower]

#print axioms finite_profile_jump
end FullRankWindow
