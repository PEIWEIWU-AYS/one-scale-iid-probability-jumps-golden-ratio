import Height
import UpperTransfer
import LeftContinuity

open IidJumpSpectra IidStaircase Filter Set
open scoped Topology

namespace IidInfiniteJumps

/-- Explicit two-sided bounds on the deficit for the unrestricted iid law. -/
theorem inverse_log_bounds {c : ℝ} (hc : 1 < c) (hc' : c < 2) :
    1 / (3 * (logDepth c + 1)) ≤ 2/3 - extremal 2 c ∧
    2/3 - extremal 2 c ≤ 1/(2*logDepth c) + 1/(6*(logDepth c)^2) := by
  obtain ⟨n,hn,hN,hu,hl⟩ := depth_window hc hc'
  have u := extremal_upper_at_height hc hc'.le (Nat.zero_lt_succ n) hu
  have l := lower_bound hc hc'.le hl
  have hpos := logDepth_pos hc hc'
  have hNpos : (0:ℝ) < n+1 := by positivity
  push_cast at u
  constructor
  · have hi : 1/(3 * (logDepth c + 1)) ≤ 1/(3 * ((n : ℝ) + 1)) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    calc
      _ ≤ 1/(3 * ((n : ℝ) + 1)) := hi
      _ = (1/((n : ℝ)+1))/3 := by field_simp; ring
      _ ≤ _ := by linarith
  · have h₁ : 1/(2*((n:ℝ)+1)) ≤ 1/(2*logDepth c) := by
      apply one_div_le_one_div_of_le (by positivity); linarith
    have h₂ : 1/(6*((n:ℝ)+1)^2) ≤ 1/(6*(logDepth c)^2) := by
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
    linarith

private noncomputable def approachTwo (n : ℕ) : ℝ := 2 - (1/2:ℝ)^(n+1)

private theorem approach_bounds (n : ℕ) :
    1 < approachTwo n ∧ approachTwo n < 2 ∧
      2-approachTwo n < (approachTwo n)⁻¹ ^ n := by
  have ha : 0 < (1/2:ℝ)^(n+1) := by positivity
  have hb : (1/2:ℝ)^(n+1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hc : 1 < approachTwo n := by dsimp [approachTwo]; linarith
  have hc' : approachTwo n < 2 := by dsimp [approachTwo]; linarith
  refine ⟨hc,hc',?_⟩
  have hp : (1/2:ℝ) ≤ (approachTwo n)⁻¹ := by
    rw [← one_div (approachTwo n)]
    exact one_div_le_one_div_of_le (by linarith) hc'.le
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hp n
  have hlt : (1/2:ℝ)^(n+1) < (1/2:ℝ)^n := by
    rw [pow_succ]
    nlinarith [show 0 < (1/2:ℝ)^n by positivity]
  simpa [approachTwo] using hlt.trans_le hpow

private theorem ladder_limit :
    Tendsto (fun n : ℕ => (2/3:ℝ) - 1/(2*((n:ℝ)+1)) - 1/(6*((n:ℝ)+1)^2))
      atTop (𝓝 (2/3)) := by
  have hi := (tendsto_one_div_add_atTop_nhds_zero_nat)
  have h₁ := hi.div_const 2
  have h₂ := (hi.pow 2).div_const 6
  have hh := ((tendsto_const_nhds (x := (2/3:ℝ))).sub h₁).sub h₂
  convert hh using 2
  · dsimp
    simp only [one_div, mul_inv_rev, inv_pow]
    ring
  · norm_num

/-- In every left neighborhood of two the unrestricted extremum takes a
strictly larger value than at its left endpoint. -/
theorem larger_before_two {a : ℝ} (ha : a < 2) :
    ∃ b, a < b ∧ b < 2 ∧ extremal 2 a < extremal 2 b := by
  let r := max a (3/2:ℝ)
  have hr₁ : 1 < r := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hr₂ : r < 2 := max_lt ha (by norm_num)
  have hpos := logDepth_pos hr₁ hr₂
  have hdef := (inverse_log_bounds hr₁ hr₂).1
  have hr : extremal 2 r < 2/3 := by
    linarith [show 0 < 1/(3*(logDepth r+1)) by positivity]
  have h := ladder_limit.eventually_const_lt hr
  obtain ⟨n,hn⟩ := h.exists
  obtain ⟨h₁,h₂,h₃⟩ := approach_bounds n
  have he := hn.trans_le (lower_bound h₁ h₂.le h₃)
  have hab := (extremal_mono 2 (le_max_left a (3/2:ℝ))).trans_lt he
  exact ⟨_,lt_of_not_ge (fun h => (not_lt_of_ge (extremal_mono 2 h)) hab),h₂,hab⟩

theorem infinitely_many_values {a : ℝ} (ha : a < 2) :
    ((extremal 2) '' Set.Ioo a 2).Infinite := by
  intro hfin
  obtain ⟨u,hu,hu2,_⟩ := larger_before_two ha
  have hne : ((extremal 2) '' Set.Ioo a 2).Nonempty := ⟨_,u,⟨hu,hu2⟩,rfl⟩
  obtain ⟨z,hz,hmax⟩ := hfin.exists_maximal_wrt id _ hne
  obtain ⟨b,⟨hab,hb⟩,rfl⟩ := hz
  obtain ⟨d,hbd,hd,hS⟩ := larger_before_two hb
  have hmem : extremal 2 d ∈ (extremal 2) '' Set.Ioo a 2 := ⟨d,⟨hab.trans hbd,hd⟩,rfl⟩
  have hh := hmax _ hmem hS.le
  exact hS.ne hh

#print axioms inverse_log_bounds
#print axioms infinitely_many_values
end IidInfiniteJumps
