import OneScaleJumpSize

open Set Filter
open scoped Topology
noncomputable section
namespace OneScale

private lemma golden_square_root : golden^2=golden+1 := by
  unfold golden; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]
private lemma golden_upper_root : golden<2 := by
  unfold golden; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5),Real.sqrt_nonneg 5]
private lemma golden_lower_root : 3/2<golden := by
  unfold golden; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5),Real.sqrt_nonneg 5]

private lemma rung_endpoints (N : ℕ) : (0<N → 1<rung 1 N) ∧ rung golden N<golden := by
  have hφ := one_lt_golden
  have h0 : 0<golden := by linarith
  have step {t : ℝ} (ht : t<golden) : (1+t)/golden<golden := by
    apply (div_lt_iff₀ h0).2
    nlinarith [golden_square_root]
  induction N using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|n; · exact ⟨by omega, hφ⟩
    rcases n with _|n; · exact ⟨by norm_num [rung,ladderValue],step hφ⟩
    rcases n with _|n; · exact ⟨by norm_num [rung,ladderValue],step (step hφ)⟩
    rcases n with _|n; · exact ⟨by norm_num [rung,ladderValue],step (step (step hφ))⟩
    rcases n with _|n
    · refine ⟨by norm_num [rung,branchValue],?_⟩
      change 4/golden^2<golden
      apply (div_lt_iff₀ (sq_pos_of_pos h0)).2
      rw [golden_square_root]
      nlinarith [golden_square_root,golden_lower_root]
    · obtain ⟨hl,hg⟩ := ih (n+3) (by omega)
      refine ⟨?_,step hg⟩
      change _ → 1 < (1+rung 1 (n+3))/1
      intro _
      linarith [hl (by omega)]

/-- Each positive integer rung has a unique crossing in the open interval (1,φ). -/
theorem rung_root_existsUnique (N : ℕ) (hN : 0<N) :
    ∃! c : ℝ, c ∈ Ioo 1 golden ∧ rung c N=c := by
  let f (c : ℝ) := rung c N-c
  have hc : ContinuousOn f (Icc 1 golden) := by
    intro c hi
    exact ((rung_continuousAt N (show c≠0 by linarith [hi.1])).sub continuousAt_id).continuousWithinAt
  obtain ⟨h1,hφ⟩ := rung_endpoints N
  obtain ⟨c,hcI,hroot⟩ := intermediate_value_Icc' one_lt_golden.le hc
    (show (0:ℝ)∈Icc (f golden) (f 1) from ⟨sub_nonpos.mpr hφ.le, sub_nonneg.mpr (h1 hN).le⟩)
  have hit : rung c N=c := sub_eq_zero.mp hroot
  have lo : 1<c := lt_of_le_of_ne hcI.1 (by rintro rfl; linarith [h1 hN])
  have hi : c<golden := lt_of_le_of_ne hcI.2 (by rintro rfl; linarith)
  refine ⟨c,⟨⟨lo,hi⟩,hit⟩,?_⟩
  rintro t ⟨⟨ht,htg⟩,eqt⟩
  rcases lt_trichotomy t c with h|h|h
  · have hh := rung_antitone_coeff N ht h.le (hi.trans golden_upper_root).le
    linarith
  · exact h
  · have hh := rung_antitone_coeff N lo h.le (htg.trans golden_upper_root).le
    linarith

/-- The crossing indexed by its rank, with rank zero at the endpoint 1. -/
def rungRoot : ℕ → ℝ
  | 0 => 1
  | n+1 => Classical.choose (rung_root_existsUnique (n+1) (by omega)).exists

theorem rungRoot_spec {N : ℕ} (hN : 0<N) :
    rungRoot N ∈ Ioo 1 golden ∧ rung (rungRoot N) N=rungRoot N := by
  cases N with
  | zero => omega
  | succ n => exact Classical.choose_spec (rung_root_existsUnique (n+1) (by omega)).exists

theorem rungRoot_strictMono : StrictMono rungRoot := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨⟨hl,hg⟩,hit⟩ := rungRoot_spec (Nat.zero_lt_succ n)
  by_cases hn : n=0
  · subst n; exact hl
  obtain ⟨⟨hl',hg'⟩,hit'⟩ := rungRoot_spec (Nat.pos_of_ne_zero hn)
  by_contra! h
  have hanti := rung_antitone_coeff (n+1) hl h (hg'.trans golden_upper_root).le
  have hnext := rung_strictMono hl' hg' (Nat.lt_succ_self n)
  rw [hit'] at hnext
  rw [hit] at hanti
  linarith

/-- The unique crossings increase to the golden ratio. -/
theorem rungRoot_tendsto_golden : Tendsto rungRoot atTop (𝓝 golden) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨c,hac,hcg⟩ := exists_between (max_lt ha one_lt_golden)
    have h1 := (le_max_right a 1).trans_lt hac
    obtain ⟨N,active,_⟩ := beta_integer_ranks h1 hcg
    have first : c ≤ rung c N := le_of_not_gt fun hh => (lt_irrefl N) ((active N).mpr hh)
    filter_upwards [eventually_ge_atTop (N+1)] with n hn
    have greater := first.trans_lt (rung_strictMono h1 hcg (show N<n by omega))
    obtain ⟨⟨hl,hg⟩,hit⟩ := rungRoot_spec (show 0<n by omega)
    have hcr : c<rungRoot n := by
      by_contra! h
      have hanti := rung_antitone_coeff n hl h (hcg.trans golden_upper_root).le
      rw [hit] at hanti
      linarith
    exact ((le_max_left a 1).trans_lt hac).trans hcr
  · intro b hb
    apply Eventually.of_forall
    intro n
    cases n with
    | zero => exact one_lt_golden.trans hb
    | succ n => exact (rungRoot_spec (Nat.zero_lt_succ n)).1.2.trans hb

#print axioms rung_root_existsUnique
#print axioms rungRoot_strictMono
#print axioms rungRoot_tendsto_golden
end OneScale
