import CollisionLimit
import FiniteRanks
import Mathlib.Tactic

open IidJumpSpectra Filter
open scoped Topology

namespace IidStaircase

/-- The correction resulting from allowing repeated labels in a sample of size N
vanishes. Its limit is the unconditional probability bound for three draws. -/
theorem rank_envelope_tendsto (a : ℝ) :
    Tendsto (fun N : ℕ => a * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / (6 * (N : ℝ)^2))
      atTop (𝓝 (a / 3)) := by
  have h : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have h₁ := (tendsto_const_nhds (x := (1:ℝ))).add h
  have h₂ := (tendsto_const_nhds (x := (2:ℝ))).add h
  have ha := (((tendsto_const_nhds (x := a)).mul h₁).mul h₂).div_const 6
  norm_num at ha
  apply (show Tendsto (fun n : ℕ => a * (1 + 1 / (n : ℝ)) * (2 + 1 / (n : ℝ)) / 6)
      atTop (𝓝 (a/3)) by convert ha using 1 <;> ring).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : (0:ℝ) < n := by exact_mod_cast hn
  field_simp [hpos.ne']
  ring_nf
  simp

/-- Transfer a deterministic finite-rank inequality to the supremum over all
Borel probability measures; the iid empirical approximation has vanishing error. -/
theorem extremal_upper_of_ranks {c a : ℝ}
    (hfin : ∀ (N : ℕ) [NeZero N] (x : Fin N → ℝ), (∀ i, 0 ≤ x i) →
      frequency (winsSet (m := 2) x c) ≤ a * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) /
        (6 * (N : ℝ)^2)) : extremal 2 c ≤ a/3 := by
  have he : Tendsto (fun N : ℕ => 1 - survival 3 N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (survival_tendsto 3)
  have htotal := (rank_envelope_tendsto a).add he
  rw [add_zero] at htotal
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds htotal
  intro N
  by_cases hn : N = 0
  · subst N
    simp [survival, extremal_le_one]
  · letI : NeZero N := ⟨hn⟩
    by_contra! hf
    obtain ⟨x, hx, hx'⟩ := exists_sample_above (m := 2) (N := N) (c := c)
      (b := a * ((N:ℝ)+1) * (2*(N:ℝ)+1) / (6 * (N:ℝ)^2)) (by linarith)
    exact (not_lt_of_ge (hfin N x hx)) hx'

/-- The cut points are normalized partial geometric sums. -/
theorem rankCut_closed {c : ℝ} (hc : 0 < c) (m : ℕ) :
    (c-1) * rankCut c m = 1 - (c⁻¹)^m := by
  induction m with
  | zero => simp [rankCut]
  | succ m ih =>
    rw [rankCut, pow_succ]
    calc
      (c-1) * ((1 + rankCut c m)/c) = ((c-1) + (c-1)*rankCut c m)/c := by ring
      _ = (c - (c⁻¹)^m)/c := by rw [ih]; ring
      _ = 1 - (c⁻¹)^m * c⁻¹ := by rw [div_eq_mul_inv, sub_mul, mul_inv_cancel₀ hc.ne']

theorem one_le_rankCut_iff {c : ℝ} (hc : 1 < c) (m : ℕ) :
    1 ≤ rankCut c m ↔ (c⁻¹)^m ≤ 2-c := by
  have hcut := rankCut_closed (show 0 < c by linarith) m
  have hpos := sub_pos.mpr hc
  constructor
  · intro h
    have hprod := mul_le_mul_of_nonneg_left h hpos.le
    linarith
  · intro h
    apply (le_of_mul_le_mul_left ?_ hpos : (1:ℝ) ≤ rankCut c m)
    linarith

/-- Finite ranks bound the success probability uniformly over every Borel iid law. -/
theorem extremal_upper_at_height {c : ℝ} {m : ℕ} (hc : 1 < c) (hc2 : c ≤ 2)
    (hm : 0 < m) (h : (c⁻¹)^m ≤ 2-c) :
    extremal 2 c ≤ (2 - 1 / (m:ℝ)) / 3 := by
  apply extremal_upper_of_ranks
  intro N hn x hx
  exact finite_upper hm (show 0 < c by linarith) hc2 ((one_le_rankCut_iff hc m).2 h) x hx

#print axioms extremal_upper_at_height

end IidStaircase
