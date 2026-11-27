import CollisionLimit
import LeftContinuity
import Mathlib.Tactic

open Finset Filter Set
open scoped Topology
open IidJumpSpectra
noncomputable section

namespace IidStaircase

private def attainableCounts (m N : ℕ) (c : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (Fintype.card (Comparison m N) + 1)).filter (fun v =>
    ∃ x : Fin N → ℝ, (∀ i, 0 ≤ x i) ∧ (winsSet (m := m) x c).card = v)

private theorem count_mem {m N : ℕ} (c : ℝ) (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (winsSet (m := m) x c).card ∈ attainableCounts m N c := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _)), x,hx,rfl⟩

private theorem counts_nonempty (m N : ℕ) (c : ℝ) : (attainableCounts m N c).Nonempty :=
  ⟨_, count_mem c (fun _ => 0) (fun _ => le_rfl)⟩

def maxWins (m N : ℕ) (c : ℝ) : ℕ :=
  (attainableCounts m N c).max' (counts_nonempty m N c)

/-- The largest win probability of a uniform law on N labelled nonnegative
values, allowing coincident values. -/
def finiteProfile (m N : ℕ) (c : ℝ) : ℝ := (maxWins m N c : ℝ) / (N : ℝ)^(m+1)

theorem maxWins_realized (m N : ℕ) (c : ℝ) :
    ∃ x : Fin N → ℝ, (∀ i, 0 ≤ x i) ∧ (winsSet (m := m) x c).card = maxWins m N c := by
  classical
  exact (Finset.mem_filter.mp ((attainableCounts m N c).max'_mem (counts_nonempty m N c))).2

private theorem count_le {m N : ℕ} (c : ℝ) (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (winsSet (m := m) x c).card ≤ maxWins m N c :=
  Finset.le_max' _ _ (count_mem c x hx)

theorem finiteProfile_le {m N : ℕ} [NeZero N] (c : ℝ) : finiteProfile m N c ≤ extremal m c := by
  obtain ⟨x, hx, he⟩ := maxWins_realized m N c
  simpa [frequency, finiteProfile, he] using frequency_le_extremal (m := m) x hx c

private theorem frequency_le_finiteProfile {m N : ℕ} (c : ℝ) (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) :
    frequency (winsSet (m := m) x c) ≤ finiteProfile m N c := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast count_le (m := m) c x hx

theorem maxWins_mono (m N : ℕ) : Monotone (maxWins m N) := by
  intro s t hst
  obtain ⟨x,hx,he⟩ := maxWins_realized m N s
  have hsub : winsSet (m := m) x s ⊆ winsSet x t := by
    intro q hq
    apply winsSet_mem.mpr
    exact (winsSet_mem.mp hq).trans_le (mul_le_mul_of_nonneg_right hst (hx _))
  rw [← he]
  exact (Finset.card_le_card hsub).trans (count_le t x hx)

private theorem match_to_left (m N : ℕ) (c : ℝ) :
    ∃ b < c, maxWins m N b = maxWins m N c := by
  obtain ⟨x,hx,he⟩ := maxWins_realized m N c
  obtain ⟨b,hb,hsub⟩ := exists_lower_sample (m := m) x c
  refine ⟨b,hb,le_antisymm (maxWins_mono m N hb.le) ?_⟩
  rw [← he]
  exact (Finset.card_le_card hsub).trans (count_le b x hx)

/-- If the integer optimum strictly increases, the first increase occurs at a
right jump of the finite-sample profile of at least one score unit. -/
theorem finiteProfile_jump_of_increase {m N : ℕ} [NeZero N] {s t : ℝ}
    (h : maxWins m N s < maxWins m N t) : ∃ b ∈ Set.Ico s t,
      RightJump (finiteProfile m N) b (1 / (N : ℝ)^(m+1)) ∧
      ¬ ContinuousAt (finiteProfile m N) b := by
  let A : Set ℝ := {u | maxWins m N s < maxWins m N u}
  have hmem : t ∈ A := h
  have hlow : s ∈ lowerBounds A := by
    intro u hu
    by_contra! hh
    exact (not_lt_of_ge (maxWins_mono m N hh.le)) hu
  let b := sInf A
  have hsb : s ≤ b := le_csInf ⟨t,hmem⟩ hlow
  have hbA (u : ℝ) (hu : u ∈ A) : b ≤ u := csInf_le ⟨s,hlow⟩ hu
  have hleft (u : ℝ) (hu : u ∈ A) : ∃ v ∈ A, v < u := by
    obtain ⟨v,hv,hve⟩ := match_to_left m N u
    refine ⟨v, ?_, hv⟩
    change maxWins m N s < maxWins m N v
    rw [hve]
    exact hu
  obtain ⟨v,hv,hvt⟩ := hleft t hmem
  have hbt : b < t := (hbA v hv).trans_lt hvt
  have hbscore : maxWins m N b = maxWins m N s := by
    refine le_antisymm ?_ (maxWins_mono m N hsb)
    apply le_of_not_gt
    intro hbad
    obtain ⟨v,hv,hvb⟩ := hleft b hbad
    exact (not_lt_of_ge (hbA v hv)) hvb
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hJ : 0 < 1 / (N : ℝ)^(m+1) := by positivity
  have hj : RightJump (finiteProfile m N) b (1 / (N : ℝ)^(m+1)) := by
    intro u hu
    obtain ⟨w, hw, hwu⟩ := exists_lt_of_csInf_lt (show A.Nonempty from ⟨t, hmem⟩) (show sInf A < u from hu)
    have hx : maxWins m N b + 1 ≤ maxWins m N u := by
      rw [hbscore]
      exact Nat.succ_le_of_lt (lt_of_lt_of_le hw (maxWins_mono m N hwu.le))
    unfold finiteProfile
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hx
  refine ⟨b,⟨hsb,hbt⟩,hj,?_⟩
  intro hcont
  have ev : ∀ᶠ u in 𝓝[>] b, finiteProfile m N u < finiteProfile m N b + 1 / (N : ℝ)^(m+1) :=
    (hcont.tendsto.eventually_lt_const (by linarith)).filter_mono nhdsWithin_le_nhds
  have right : ∀ᶠ u in 𝓝[>] b, b < u := self_mem_nhdsWithin
  obtain ⟨u,hu,hsmall⟩ := (right.and ev).exists
  exact (not_lt_of_ge (hj u hu)) hsmall

/-- On every interval of genuine Borel-law growth, all sufficiently large
uniform finite-sample optima have an actual discontinuity. -/
theorem eventually_finiteProfile_jump {m : ℕ} {s t : ℝ}
    (h : extremal m s < extremal m t) :
    ∀ᶠ N : ℕ in atTop, ∃ b ∈ Set.Ico s t,
      RightJump (finiteProfile m N) b (1 / (N : ℝ)^(m+1)) ∧
      ¬ ContinuousAt (finiteProfile m N) b := by
  have he : ∀ᶠ N : ℕ in atTop, 1 - (extremal m t - extremal m s) < survival (m+1) N :=
    (survival_tendsto (m+1)).eventually_const_lt (by linarith)
  filter_upwards [he, eventually_ge_atTop 1] with N hsurv hN
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨x,hx,hlo⟩ := exists_sample_above (N := N) (m := m) (c := t) (b := extremal m s)
    (by linarith)
  have hinc := (finiteProfile_le (N := N) s).trans_lt (hlo.trans_le (frequency_le_finiteProfile t x hx))
  apply finiteProfile_jump_of_increase
  have hpos : 0 < (N : ℝ)^(m+1) := by positivity
  have hcast := (div_lt_div_iff_of_pos_right hpos).mp hinc
  exact_mod_cast hcast

/-- Finitely many pairwise disjoint intervals of increase force distinct
finite-profile jumps simultaneously at every sufficiently large sample size. -/
theorem eventually_many_finiteProfile_jumps {m K : ℕ} (s t : Fin K → ℝ)
    (hg : ∀ i, extremal m (s i) < extremal m (t i))
    (hd : ∀ i j, i ≠ j → Disjoint (Set.Ico (s i) (t i)) (Set.Ico (s j) (t j))) :
    ∀ᶠ N : ℕ in atTop, ∃ b : Fin K ↪ ℝ, ∀ i,
      b i ∈ Set.Ico (s i) (t i) ∧ RightJump (finiteProfile m N) (b i) (1/(N:ℝ)^(m+1)) ∧
      ¬ ContinuousAt (finiteProfile m N) (b i) := by
  classical
  have he := Filter.eventually_all.mpr (fun i => eventually_finiteProfile_jump (hg i))
  filter_upwards [he] with N hN
  choose b hb hj using hN
  have hinj : Function.Injective b := by
    intro i j heq
    by_contra hne
    exact (Set.disjoint_left.mp (hd i j hne)) (hb i) (heq.symm ▸ hb j)
  exact ⟨⟨b,hinj⟩, fun i => ⟨hb i, hj i⟩⟩

#print axioms eventually_finiteProfile_jump
#print axioms eventually_many_finiteProfile_jumps
end IidStaircase
