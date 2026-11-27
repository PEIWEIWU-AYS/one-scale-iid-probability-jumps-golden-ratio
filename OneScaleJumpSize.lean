import OneScaleTailReductionRanks
import OneScaleJumps

open Filter Set
open scoped Topology
noncomputable section
namespace OneScale

private def rungTree : ℕ → ThresholdTree
  | 0 => .leaf
  | 1 => .node .leaf .leaf
  | 2 => .node .leaf (rungTree 1)
  | 3 => .node .leaf (rungTree 2)
  | 4 => .node (rungTree 1) (rungTree 1)
  | n+5 => .node .leaf (rungTree (n+3))

private theorem rungTree_value (s : ℝ) (n : ℕ) : (rungTree n).value s = rung s n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|n; · rfl
    rcases n with _|n; · rfl
    rcases n with _|n; · rfl
    rcases n with _|n; · rfl
    rcases n with _|n
    · simp [rungTree,rung,ThresholdTree.value,branchValue]; ring
    · change (1+(rungTree (n+3)).value s)/s = (1+rung s (n+3))/s
      rw [ih (n+3) (by omega)]

private theorem tree_anti (T : ThresholdTree) {a b : ℝ} (ha : 1 < a) (hab : a≤b)
    (hb : b≤2) : T.value b ≤ T.value a := by
  induction T with
  | leaf => exact le_rfl
  | node l r il ir =>
    have hp : 0 ≤ l.value b + r.value b := by
      linarith [ThresholdTree.one_le_value (show 0<b by linarith) hb l,
        ThresholdTree.one_le_value (show 0<b by linarith) hb r]
    change (l.value b+r.value b)/b ≤ (l.value a+r.value a)/a
    exact (div_le_div_of_nonneg_left hp (by linarith) hab).trans
      (div_le_div_of_nonneg_right (add_le_add il ir) (by linarith))

/-- The common finite optimization problem for all coefficients with N active levels. -/
def rankMaximum (N : ℕ) : ℝ := sSup {b : ℝ | ∃ w : Fin N → ℝ, Mass w ∧ rankScore w=b}

/-- The finite cubic attains its maximum on every nonempty rank simplex. -/
theorem rankMaximum_attained {N : ℕ} (hn : 0<N) :
    IsGreatest {b : ℝ | ∃ w : Fin N → ℝ, Mass w ∧ rankScore w=b} (rankMaximum N) := by
  classical
  have cont : Continuous (@rankScore N) := by
    unfold rankScore
    apply continuous_finset_sum; intro i _
    apply continuous_finset_sum; intro j _
    apply continuous_finset_sum; intro k _
    split_ifs <;> fun_prop
  have ne : (stdSimplex ℝ (Fin N)).Nonempty := ⟨_,single_mem_stdSimplex ℝ (⟨0,hn⟩ : Fin N)⟩
  obtain ⟨w,hw,hm⟩ := (isCompact_stdSimplex (Fin N)).exists_isMaxOn ne cont.continuousOn
  have best : IsGreatest {b : ℝ | ∃ v : Fin N → ℝ, Mass v ∧ rankScore v=b} (rankScore w) :=
    ⟨⟨w,hw,rfl⟩,by rintro _ ⟨v,hv,rfl⟩; exact hm hv⟩
  simpa only [rankMaximum,best.csSup_eq] using best

private theorem beta_eq_rankMaximum {s : ℝ} (hs : 1<s) (hg : s<golden) {N : ℕ}
    (active : ∀ i, i<N ↔ rung s i<s) : beta s = rankMaximum N := by
  obtain ⟨M,hM,hm⟩ := beta_integer_ranks hs hg
  have eq : M=N := by
    apply Nat.le_antisymm
    · by_contra! hh
      exact (Nat.lt_irrefl N) ((active N).2 ((hM N).1 hh))
    · by_contra! hh
      exact (Nat.lt_irrefl M) ((hM M).2 ((active M).1 hh))
  subst M
  exact hm.csSup_eq.symm

/-- At the Nth threshold the probability equals the N-rank maximum.
On a full right neighborhood it equals the (N+1)-rank maximum. -/
theorem rank_transition {c : ℝ} (hc : 1<c) (hg : c<golden) {N : ℕ}
    (hit : rung c N=c) : beta c=rankMaximum N ∧
      ∀ᶠ s in 𝓝[>] c, beta s=rankMaximum (N+1) := by
  have hm := rung_strictMono hc hg
  refine ⟨beta_eq_rankMaximum hc hg (fun i => by simpa only [hit] using (hm.lt_iff_lt (a:=i) (b:=N)).symm), ?_⟩
  have large : c < rung c (N+1) := by simpa only [hit] using hm (Nat.lt_succ_self N)
  have hcont : ContinuousAt (fun s => rung s (N+1)) c := by
    simpa only [← rungTree_value] using ThresholdTree.value_continuousAt (ne_of_gt (by linarith : 0<c)) (rungTree (N+1))
  have gap : ∀ᶠ s in 𝓝 c, s < rung s (N+1) :=
    continuousAt_id.tendsto.eventually_lt hcont.tendsto large
  have stay : ∀ᶠ s in 𝓝 c, s<golden := gt_mem_nhds hg
  filter_upwards [self_mem_nhdsWithin (s:=Ioi c),
    (gap.and stay).filter_mono nhdsWithin_le_nhds] with s hcs hs
  change c<s at hcs
  have hs2 : s≤2 := by
    have hh := (before_golden (hc.trans hcs)).1 hs.2
    nlinarith [sq_nonneg (s-1)]
  have enter : rung s N < s := by
    have h := tree_anti (rungTree N) hc hcs.le hs2
    rw [rungTree_value,rungTree_value,hit] at h
    exact h.trans_lt hcs
  have hsm := rung_strictMono (hc.trans hcs) hs.2
  apply beta_eq_rankMaximum (hc.trans hcs) hs.2
  intro i
  constructor
  · intro hi
    exact (hsm.monotone (by omega : i≤N)).trans_lt enter
  · intro hi
    exact lt_of_not_ge (fun hn => (not_lt_of_ge (hs.1.le.trans (hsm.monotone hn))) hi)

/-- Exact right jump size on the original strict staircase, including zero. -/
theorem rank_jump_iff {c g : ℝ} (hc : 1<c) (hg : c<golden) {N : ℕ} (hit : rung c N=c) :
    IidJumpSpectra.RightJump beta c g ↔ g ≤ rankMaximum (N+1)-rankMaximum N := by
  obtain ⟨atC,after⟩ := rank_transition hc hg hit
  have right : ∀ᶠ t in 𝓝[>] c, c<t := self_mem_nhdsWithin
  constructor
  · intro jump
    obtain ⟨s,hc',hv⟩ := (right.and after).exists
    have h := jump s hc'
    change beta c + g ≤ beta s at h
    linarith
  · intro h s hs
    have less : ∀ᶠ t in 𝓝[>] c, t<s := (gt_mem_nhds hs).filter_mono nhdsWithin_le_nhds
    obtain ⟨t,ht,hv,hct⟩ := (less.and (after.and right)).exists
    have comp := beta_mono (hc.trans hct) ht.le
    change beta c + g ≤ beta s
    linarith

#print axioms rank_jump_iff
/-- Continuity of each threshold rung away from a zero coefficient. -/
theorem rung_continuousAt (n : ℕ) {c : ℝ} (hc : c≠0) :
    ContinuousAt (fun t => rung t n) c := by
  simpa only [← rungTree_value] using ThresholdTree.value_continuousAt hc (rungTree n)

/-- Increasing the coefficient lowers the value of each rung. -/
theorem rung_antitone_coeff (n : ℕ) {a b : ℝ} (ha : 1<a) (hab : a≤b) (hb : b≤2) :
    rung b n ≤ rung a n := by
  simpa only [← rungTree_value] using tree_anti (rungTree n) ha hab hb

end OneScale
