import EndpointAsymptotics.RankModelJump
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Set
open scoped Topology
noncomputable section
namespace FullRankWindow

private theorem threshold_exists (n : ℕ) :
    ∃ c : ℝ, 3/2<c ∧ c<2 ∧ (2-c)*c^(n+2)=1 := by
  let f (x : ℝ) := (2-x)*x^(n+2)
  have big : 1<f (3/2) := by
    have pow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤3/2) (show 2≤n+2 by omega)
    dsimp only [f]
    nlinarith only [pow]
  have endval : f 2=0 := by simp [f]
  have cont : ContinuousOn f (Icc (3/2) 2) := by dsimp [f]; fun_prop
  obtain ⟨c,hc,h⟩ := intermediate_value_Icc' (by norm_num : (3/2:ℝ)≤2) cont
    (show (1:ℝ) ∈ Icc (f 2) (f (3/2)) from ⟨by rw [endval];norm_num,big.le⟩)
  refine ⟨c,lt_of_le_of_ne hc.1 ?_,lt_of_le_of_ne hc.2 ?_,h⟩
  · intro he; rw [←he] at h; linarith only [big,h]
  · intro he; rw [he,endval] at h;norm_num at h

private theorem ordered_roots {m n : ℕ} (hmn : m<n) {c d : ℝ}
    (hc : 1<c) (h2 : c<2) (hd : 1<d)
    (cr : (2-c)*c^(m+2)=1) (dr : (2-d)*d^(n+2)=1) : c<d := by
  have hi : 1<(2-c)*c^(n+2) := by
    rw [←cr]
    exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hc (by omega : m+2<n+2)) (sub_pos.mpr h2)
  by_contra! h
  rcases eq_or_lt_of_le h with rfl | hdc
  · linarith only [hi,dr]
  · have lo := threshold_opens_right (n:=n+1) hd hdc dr
    linarith only [hi,lo]

/-- Infinitely many different positive jump coefficients for the increasing
family of finite-block models. The profile indexed by k+1 allows k+2 labels. -/
theorem jumps_along_finite_models :
    ∃ c : ℕ → ℝ, StrictMono c ∧ Tendsto c atTop (𝓝 2) ∧
      ∀ k, 1<c k ∧ c k<2 ∧ (2-c k)*(c k)^(k+2)=1 ∧
        ∃ g : ℝ, 0<g ∧ ∀ d, c k<d → d<2 →
          finiteBlockProfile (k+1) (c k)+g≤finiteBlockProfile (k+1) d := by
  choose c h0 h2 hr using threshold_exists
  have one (k : ℕ) : 1<c k := by linarith only [h0 k]
  refine ⟨c,fun m n h => ordered_roots h (one m) (h2 m) (one n) (hr m) (hr n),?_,
    fun k => ⟨one k,h2 k,hr k,finite_profile_jump (one k) (h2 k) (hr k)⟩⟩
  have lim0 : Tendsto (fun n : ℕ => 2-c n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sub_nonneg.mpr (h2 n).le) (g:=fun n : ℕ => (2/3:ℝ)^n)
    · intro n
      have cp : 0<c n := by linarith only [one n]
      have val : 2-c n=(c n)⁻¹^(n+2) := by
        rw [inv_pow,←one_div]
        exact (eq_div_iff (pow_ne_zero _ cp.ne')).2 (hr n)
      rw [val]
      have hv : (c n)⁻¹≤2/3 := by
        rw [←one_div]
        apply (div_le_iff₀ cp).2
        linarith only [h0 n]
      exact (pow_le_pow_left₀ (inv_nonneg.mpr cp.le) hv _).trans
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : n≤n+2))
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using (tendsto_const_nhds (x:=(2:ℝ))).sub lim0

#print axioms jumps_along_finite_models
end FullRankWindow
