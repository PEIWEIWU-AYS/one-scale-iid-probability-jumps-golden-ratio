import Endpoint
import OneScaleLaw

open Finset OneScale IidJumpSpectra IidInfiniteJumps MeasureTheory
open scoped BigOperators
noncomputable section
namespace TerminalRescaling

/-- Subprobability weights with positive mass confined to [a,z]. Translating
that interval to start at zero makes the stricter coefficient e available. -/
theorem terminal_score_cap {n : ℕ} {c e a z : ℝ} (hc : c≤2) (ha : 0≤a)
    (width : (2-e)*(z-a)≤(2-c)*z) (x u : Fin n → ℝ)
    (hu : ∀ i, 0≤u i) (inside : ∀ i, u i≠0 → a≤x i ∧ x i≤z) :
    score c x u ≤ (∑ i, u i)^3 * extremal 2 e := by
  classical
  let q := ∑ i, u i
  have hq : 0≤q := sum_nonneg (fun i _ => hu i)
  by_cases h0 : q=0
  · have zero (i) : u i=0 := le_antisymm ((single_le_sum (fun j _ => hu j) (mem_univ i)).trans (le_of_eq h0)) (hu i)
    simp only [score,zero,mul_zero,ite_self,sum_const_zero,zero_pow (by decide : 3≠0),zero_mul,le_refl]
  have pos := lt_of_le_of_ne hq (Ne.symm h0)
  let v (i) := u i/q
  let y (i) := max 0 (x i-a)
  have hv : Mass v := ⟨fun i => div_nonneg (hu i) hq,by
    dsimp only [v];rw [←sum_div];exact div_self h0⟩
  obtain ⟨μ,hμ,_,eq⟩ := weighted_law e y v (fun i => le_max_left _ _) hv
  letI := hμ
  have cap : score e y v≤extremal 2 e := eq ▸ iidWin_le_extremal 2 e μ
  have pt (i j k : Fin n) : (if Win c x i j k then u i*u j*u k else 0) ≤
      q^3*(if Win e y i j k then v i*v j*v k else 0) := by
    by_cases hi : u i=0
    · simp [hi,v]
    by_cases hj : u j=0
    · simp [hj,v]
    by_cases hk : u k=0
    · simp [hk,v]
    by_cases win : Win c x i j k
    · have ix := inside i hi
      have jx := inside j hj
      have kx := inside k hk
      have adj : (c-e)*(x k-a)≤(2-c)*a := by
        by_cases hce : 0≤c-e
        · have bound := mul_le_mul_of_nonneg_left (sub_le_sub_right kx.2 a) hce
          nlinarith only [bound,width]
        · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hce)) (sub_nonneg.mpr kx.1)).trans
            (mul_nonneg (sub_nonneg.mpr hc) ha)
      have ew : Win e y i j k := by
        unfold Win y
        rw [max_eq_right (sub_nonneg.mpr ix.1),max_eq_right (sub_nonneg.mpr jx.1),
          max_eq_right (sub_nonneg.mpr kx.1)]
        change x i+x j<c*x k at win
        nlinarith only [adj,win]
      rw [if_pos win,if_pos ew]
      dsimp only [v]
      apply le_of_eq
      field_simp;ring
    · rw [if_neg win]
      split_ifs
      · exact mul_nonneg (pow_nonneg hq 3) (mul_nonneg (mul_nonneg (hv.1 _) (hv.1 _)) (hv.1 _))
      · simp
  have le' : score c x u ≤ q^3*score e y v := by
    simpa only [score,mul_sum] using sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => pt i j k
  exact le'.trans (mul_le_mul_of_nonneg_left cap (pow_nonneg hq 3))

/-- The translated coefficient has logarithmic depth at most the delay d. -/
theorem effective_depth {r : ℝ} (d : ℕ) (hr : 1<r)
    (gate : r*(1+(r⁻¹)^d)<2) :
    1<2-(r⁻¹)^d ∧ 2-(r⁻¹)^d<2 ∧ logDepth (2-(r⁻¹)^d)≤d := by
  let e := 2-(r⁻¹)^d
  have hr0 : 0<r := by linarith
  have hp : 0<(r⁻¹)^d := by positivity
  have er : r≤e := by
    have aux := mul_le_mul_of_nonneg_right hr.le hp.le
    dsimp only [e];nlinarith only [gate,aux]
  have he := hr.trans_le er
  have he2 : e<2 := by dsimp only [e];linarith
  refine ⟨he,he2,?_⟩
  change logDepth e≤_
  rw [logDepth,show 2-e=(r⁻¹)^d by dsimp only [e];ring,Real.log_pow,Real.log_inv]
  apply (div_le_iff₀ (Real.log_pos he)).2
  have z := mul_le_mul_of_nonneg_left (Real.log_le_log hr0 er) (Nat.cast_nonneg (α:=ℝ) d)
  linarith only [z]

#print axioms terminal_score_cap
#print axioms effective_depth
end TerminalRescaling
