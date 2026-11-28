import EndpointAsymptotics.ClosedBlockLower

open IidJumpSpectra OneScale
open scoped BigOperators
noncomputable section

namespace ClosedSpectrum

/-- Moving a positive block down by its smallest entry makes every closed
triple win strictly. The new law is admissible for the unrestricted extremum. -/
theorem closedScore_le_extremal {α : Type*} [Fintype α] [Nonempty α]
    {c : ℝ} (hc : c < 2) (x w : α → ℝ) (hx : ∀ i, 0 < x i) (hw : Mass w) :
    closedScore c x w ≤ extremal 2 c := by
  classical
  obtain ⟨a,_,hmin⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  let z (i : α) := x i - x a
  have hz (i : α) : 0 ≤ z i := sub_nonneg.mpr (hmin _ (Finset.mem_univ i))
  have wins (i j k : α) (h : x i+x j ≤ c*x k) : Win c z i j k := by
    unfold Win z
    nlinarith only [h, mul_pos (sub_pos.mpr hc) (hx a)]
  obtain ⟨μ,hμ,_,heq⟩ := weighted_law c z w hz hw
  haveI := hμ
  apply le_trans (b := score c z w)
  · unfold closedScore score
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
    by_cases h : x i+x j ≤ c*x k
    · simp [h,wins i j k h]
    · simp only [if_neg h]
      split_ifs
      · exact mul_nonneg (mul_nonneg (hw.1 _) (hw.1 _)) (hw.1 _)
      · exact le_rfl
  · rw [← heq]
    exact iidWin_le_extremal _ _ _

/-- Test for strict improvement of a benchmark by an arbitrary choice of
layer mass. The odds r are the ratio of lower mass to upper mass. -/
theorem odds_improve_iff {B Q S : ℝ} (hB : B ≤ S) (hS : 1/3 < S) :
    (∃ r : ℝ, 0 ≤ r ∧ S < (B+2*r*Q+r^2)/(1+3*r+3*r^2)) ↔
      0 < 2*Q-3*S ∧ 4*(3*S-1)*(S-B) < (2*Q-3*S)^2 := by
  let a := 3*S-1
  let b := 2*Q-3*S
  let e := S-B
  have ha : 0 < a := by dsimp [a]; linarith
  have he : 0 ≤ e := sub_nonneg.mpr hB
  have eq (r : ℝ) (hr : 0 ≤ r) :
      S < (B+2*r*Q+r^2)/(1+3*r+3*r^2) ↔ 0 < b*r-a*r^2-e := by
    rw [lt_div_iff₀ (show 0 < 1+3*r+3*r^2 by positivity)]
    dsimp [a,b,e]
    constructor <;> intro h <;> nlinarith only [h]
  change _ ↔ 0 < b ∧ 4*a*e < b^2
  constructor
  · rintro ⟨r,hr,h⟩
    have hquad := (eq r hr).1 h
    constructor
    · by_contra! hb
      nlinarith only [hquad,he,mul_nonpos_of_nonpos_of_nonneg hb hr,
        mul_nonneg ha.le (sq_nonneg r)]
    · nlinarith only [sq_nonneg (2*a*r-b), mul_pos (show 0<4*a by linarith) hquad]
  · rintro ⟨hb,hd⟩
    let r := b/(2*a)
    have hr : 0 < r := div_pos hb (by positivity)
    have harg : 2*a*r = b := by dsimp [r]; field_simp
    refine ⟨r,hr.le,(eq r hr.le).2 ?_⟩
    have hcomp : 4*a*(b*r-a*r^2-e) = b^2-4*a*e := by
      calc
        _ = b^2-(2*a*r-b)^2-4*a*e := by ring
        _ = _ := by rw [harg]; ring
    exact pos_of_mul_pos_right (hcomp.symm ▸ sub_pos.mpr hd) (by positivity)

#print axioms closedScore_le_extremal
#print axioms odds_improve_iff
end ClosedSpectrum
