import EndpointAsymptotics.StrictRankGap

open Finset OneScale ClosedSpectrum Set
open scoped BigOperators
noncomputable section
namespace FullRankWindow

/-- The compact parametrization in terms of the lower-level mass p. The
expression extends continuously to p=1, where its value is 1/3. -/
def mixScore (B Q p : ℝ) := ((1-p)^2*B+2*p*(1-p)*Q+p^2)/(1+p+p^2)

private theorem peak_nonnegative (n : ℕ) : 0≤peak n := by
  cases n with
  | zero => norm_num [peak]
  | succ n => rw [peak]; positivity

private theorem strict_improved {n : ℕ} {c : ℝ} (hc : 1<c) (h2 : c<2)
    (root : (2-c)*c^(n+1)=1) {P : RankTables (n+1)} (fe : strictFeasible c P)
    (w : Fin (n+1) → ℝ) (hw : Mass w) {p : ℝ} (hp : p∈Set.Icc 0 1) :
    ∃ q∈Set.Icc (0:ℝ) 1, mixScore (tableTriple P w) (tablePair P w) p<mixScore (peak n) 1 q := by
  have bounds := table_caps h2 fe w hw
  have hB := bounds.1.trans ((rank_peak n).2 w hw)
  have hQ := bounds.2
  have hpeak := peak_lt (n:=n)
  have hpos := peak_nonnegative n
  rcases eq_or_lt_of_le hp.1 with h | hp0
  · subst p
    let q := (2-3*peak n)/2
    have hq : 0<q := by dsimp only [q]; linarith
    have hq1 : q≤1 := by dsimp only [q];linarith
    refine ⟨q,⟨hq.le,hq1⟩,?_⟩
    simp only [mixScore,sub_zero,one_pow,one_mul,mul_zero,zero_mul,zero_pow (by decide : 2≠0),
      add_zero,div_one]
    apply lt_of_le_of_lt hB
    apply (lt_div_iff₀ (by positivity)).2
    have id : (1-q)^2*peak n+2*q*(1-q)*1+q^2-peak n*(1+q+q^2)=q^2 := by
      dsimp only [q];ring
    linarith only [id,sq_pos_of_pos hq]
  rcases eq_or_lt_of_le hp.2 with h | hp1
  · subst p
    refine ⟨1/2,by constructor <;> norm_num,?_⟩
    norm_num [mixScore]
    linarith
  · refine ⟨p,hp,?_⟩
    unfold mixScore
    apply (div_lt_div_iff_of_pos_right (by positivity : 0<1+p+p^2)).2
    have coefB : 0<(1-p)^2 := sq_pos_of_pos (sub_pos.mpr hp1)
    have coefQ : 0<2*p*(1-p) := mul_pos (mul_pos (by norm_num) hp0) (sub_pos.mpr hp1)
    rcases strict_table_misses hc h2 root fe w hw with loss | loss
    · linarith only [mul_lt_mul_of_pos_left loss coefB,mul_le_mul_of_nonneg_left hQ coefQ.le]
    · linarith only [mul_le_mul_of_nonneg_left hB coefB.le,mul_lt_mul_of_pos_left loss coefQ]

private def domain (m : ℕ) := (stdSimplex ℝ (Fin m)) ×ˢ Set.Icc (0:ℝ) 1

private def evalTable {m : ℕ} (P : RankTables m) (a : (Fin m → ℝ) × ℝ) :=
  mixScore (tableTriple P a.1) (tablePair P a.1) a.2

private theorem eval_cont {m : ℕ} (P : RankTables m) : ContinuousOn (evalTable P) (domain m) := by
  apply Continuous.continuousOn
  have tri : Continuous (fun a : (Fin m → ℝ) × ℝ => tableTriple P a.1) := by
    unfold tableTriple
    apply continuous_finset_sum _ (fun i _ => ?_)
    apply continuous_finset_sum _ (fun j _ => ?_)
    apply continuous_finset_sum _ (fun k _ => ?_)
    split_ifs <;> fun_prop
  have pair : Continuous (fun a : (Fin m → ℝ) × ℝ => tablePair P a.1) := by
    unfold tablePair
    apply continuous_finset_sum _ (fun i _ => ?_)
    apply continuous_finset_sum _ (fun k _ => ?_)
    split_ifs <;> fun_prop
  unfold evalTable mixScore
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    linarith only [sq_nonneg (x.2+1/2)]

/-- At a multinacci endpoint there is a uniform positive gap for the entire
fixed-cardinality model, after simultaneously optimizing comparison tables,
all probability weights, and the mixing parameter. -/
theorem strict_uniform_gap {n : ℕ} {c : ℝ} (hc : 1<c) (h2 : c<2) (root : (2-c)*c^(n+1)=1) :
    ∃ q∈Set.Icc (0:ℝ) 1, ∃ g : ℝ, 0<g ∧
      ∀ P : RankTables (n+1), strictFeasible c P → ∀ w : Fin (n+1) → ℝ, Mass w →
      ∀ p ∈ Set.Icc (0:ℝ) 1,
      mixScore (tableTriple P w) (tablePair P w) p+g ≤ mixScore (peak n) 1 q := by
  classical
  let Good := {P : RankTables (n+1) // strictFeasible c P}
  let scores : Set ℝ := ⋃ P : Good, evalTable P.val '' domain (n+1)
  have comp : IsCompact scores := isCompact_iUnion fun P =>
    ((isCompact_stdSimplex (Fin (n+1))).prod isCompact_Icc).image_of_continuousOn (eval_cont P.val)
  by_cases ne : scores.Nonempty
  · obtain ⟨z,hz,hmax⟩ := comp.exists_isMaxOn ne continuousOn_id
    have memz : ∃ (P : Good) (a : (Fin (n+1) → ℝ) × ℝ), a∈domain (n+1) ∧ evalTable P.val a=z := by
      obtain ⟨P,a,ha,he⟩ := mem_iUnion.mp hz
      exact ⟨P,a,ha,he⟩
    obtain ⟨P,a,ha,rfl⟩ := memz
    obtain ⟨q,hq,up⟩ := strict_improved hc h2 root P.property a.1 ha.1 ha.2
    refine ⟨q,hq,_,sub_pos.mpr up,?_⟩
    intro T ft w hw p hp
    have mem : evalTable T (w,p)∈scores := mem_iUnion.mpr ⟨⟨T,ft⟩,⟨(w,p),⟨hw,hp⟩,rfl⟩⟩
    have le : evalTable T (w,p) ≤ evalTable P.val a := hmax mem
    change mixScore (tableTriple T w) (tablePair T w) p ≤
      mixScore (tableTriple P.val a.1) (tablePair P.val a.1) a.2 at le
    linarith only [le]
  · refine ⟨0,⟨le_rfl,zero_le_one⟩,1,zero_lt_one,?_⟩
    intro P hP w hw p hp
    exfalso
    apply ne
    exact ⟨_,mem_iUnion.mpr ⟨⟨P,hP⟩,⟨(w,p),⟨hw,hp⟩,rfl⟩⟩⟩

#print axioms strict_uniform_gap
end FullRankWindow
