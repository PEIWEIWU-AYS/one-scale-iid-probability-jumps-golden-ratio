import EndpointAsymptotics.QuantitativeBands
import EndpointAsymptotics.QuantilePopulationTransfer
open Finset OneScale
open scoped BigOperators
noncomputable section
namespace QuantitativeBands

def bandWeight (w : Fin n → ℝ) (p : Fin n → Prop) : ℝ := by
  classical exact ∑ i ∈ univ.filter p, w i

private theorem cut_mono (w : Fin n → ℝ) (hw : ∀ i,0≤w i) (p q : Fin n → Prop)
    (pq : ∀ i,p i → q i) : bandWeight w p≤bandWeight w q := by
  classical
  exact sum_le_sum_of_subset_of_nonneg (fun i hi => mem_filter.mpr ⟨mem_univ _,pq i (mem_filter.mp hi).2⟩)
    (fun i _ _ => hw i)

/-- The assembly step for the population bound permits atoms at every band
edge and at the selected quantile. -/
theorem finite_quantile_assembly {n : ℕ} (K d : ℕ) (hd : 0<d)
    (x w : Fin n → ℝ) (hx : ∀ i, 0<x i) (hw : Mass w) (H : ℝ) (hH : 0<H)
    (ef : ∀ (z : ℝ), 0<z → ∃ t : ℕ → ℝ, Monotone t ∧ t 0=0 ∧ (∀ i,t i≤z) ∧
      (∑ i ∈ range (K+d), (bandWeight w (fun j => t i≤x j)-bandWeight w (fun j => t (i+1)≤x j))^2*
        bandWeight w (fun j => t (i+d)≤x j))≤H ∧
      (bandWeight w (fun j => t K≤x j ∧ x j≤z))^3 ≤ 3*((d:ℝ)+1)*H) :
    (2/3:ℝ)≤(Real.sqrt K+4*Real.sqrt d)*Real.sqrt H := by
  classical
  have hd' : 0<(d:ℝ) := by exact_mod_cast hd
  have sd := Real.sq_sqrt hd'.le
  have sh := Real.sq_sqrt hH.le
  by_cases big : 1≤(d:ℝ)*H
  · have root : 1≤Real.sqrt d*Real.sqrt H := by
      rw [←Real.sqrt_mul hd'.le,←Real.sqrt_one]
      exact Real.sqrt_le_sqrt big
    nlinarith only [root,mul_nonneg (Real.sqrt_nonneg (K:ℝ)) (Real.sqrt_nonneg H)]
  let ε := ((d:ℝ)*H)^((3:ℝ)⁻¹)
  have heq : ε^3=(d:ℝ)*H := Real.rpow_inv_natCast_pow (mul_pos hd' hH).le (by decide : (3:ℕ)≠0)
  have he : 0<ε := Real.rpow_pos_of_pos (mul_pos hd' hH) _
  have he1 : ε≤1 := by
    by_contra! bad
    have pow := pow_lt_pow_left₀ bad (by norm_num : (0:ℝ)≤1) (by decide : (3:ℕ)≠0)
    rw [one_pow,heq] at pow
    exact big pow.le
  obtain ⟨z,hz,strict,weak⟩ := finite_quantile x w hx hw he he1
  obtain ⟨t,mt,zero,bounded,loss,last⟩ := ef z hz
  let T i := bandWeight w (fun j => t i ≤ x j)
  have mono : Antitone T := by
    intro i j hij
    exact cut_mono w hw.1 _ _ (fun k hk => (mt hij).trans hk)
  have tail (i) : ε≤T i := weak.trans
    (cut_mono w hw.1 (fun j => z≤x j) _ (fun j h => (bounded i).trans h))
  have at0 : T 0=1 := by simp [T,bandWeight,zero,fun i => (hx i).le,hw.2]
  let q := T K-ε
  have qpos : 0≤q := sub_nonneg.mpr (tail K)
  have decomp : T K=bandWeight w (fun j => t K≤x j ∧ x j≤z)+bandWeight w (fun j => z<x j) := by
    unfold T bandWeight
    simp only [sum_filter]
    rw [←sum_add_distrib]
    apply sum_congr rfl;intro i _
    by_cases u : z<x i
    · have l := (bounded K).trans u.le
      simp [u,l,not_le.mpr u]
    · by_cases l : t K≤x i <;> simp [u,l,le_of_not_gt u]
  have qsmall : q≤bandWeight w (fun j => t K≤x j ∧ x j≤z) := by
    change bandWeight w (fun j => z<x j) ≤ ε at strict
    dsimp only [q]; linarith only [decomp,strict]
  have term : q^3≤6*(d:ℝ)*H := by
    apply (pow_le_pow_left₀ qpos qsmall 3).trans
    exact last.trans (mul_le_mul_of_nonneg_right (by
      have : 1≤(d:ℝ) := by exact_mod_cast hd
      linarith) hH.le)
  exact effective_band_bound K d T he hH.le mono tail at0 (by dsimp [q];ring) heq term loss

/-- The effective deficit, with all constants explicit, after taking a square. -/
theorem band_cap_of_root_bound (K d : ℕ) (hd : 0<d) {H p : ℝ}
    (deficit : H=2/3-p) (hH : 0≤H)
    (h : (2/3:ℝ)≤(Real.sqrt K+4*Real.sqrt d)*Real.sqrt H) :
    p ≤ 2/3 - 4/(9*(Real.sqrt K+4*Real.sqrt d)^2) := by
  let b := Real.sqrt K+4*Real.sqrt d
  have hd' : 0<(d:ℝ) := by exact_mod_cast hd
  have hb : 0<b := by dsimp [b];positivity
  have hh := mul_self_le_mul_self (by norm_num : (0:ℝ)≤2/3) h
  change 2/3*(2/3)≤(b*Real.sqrt H)*(b*Real.sqrt H) at hh
  have sq := Real.sq_sqrt hH
  change p ≤ 2/3-4/(9*b^2)
  rw [le_sub_comm,div_le_iff₀ (by positivity)]
  rw [←deficit]
  calc
    4 = (9:ℝ)*(2/3*(2/3)) := by norm_num
    _ ≤ 9*((b*Real.sqrt H)*(b*Real.sqrt H)) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = 9*(b^2*(Real.sqrt H)^2) := by ring
    _ = H*(9*b^2) := by rw [sq];ring

end QuantitativeBands
