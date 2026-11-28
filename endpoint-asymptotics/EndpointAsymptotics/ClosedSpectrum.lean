import EndpointAsymptotics.EndpointPatternUpper
import EndpointAsymptotics.ClosedBlockLower

open Finset Filter Set IidJumpSpectra OneScale
open scoped BigOperators
noncomputable section
namespace ClosedSpectrum

/-- A finite positive block can carry arbitrary positive and zero weights. -/
def blockValues (c : ℝ) : Set ℝ := {v | ∃ (n : ℕ) (x w : Fin n → ℝ) (t : ℝ),
    (∀ i, 0<x i) ∧ Mass w ∧ 0<t ∧ t≤1 ∧
      v = blockValue t (closedScore c x w) (closedPairs c x w)}

def rightValue (c : ℝ) : ℝ := sInf (extremal 2 '' Ioi c)

private theorem rightSet_ne (c : ℝ) : (extremal 2 '' Ioi c).Nonempty :=
  ⟨_,c+1,by simp,rfl⟩

private theorem rightSet_bdd (c : ℝ) : BddBelow (extremal 2 '' Ioi c) := by
  refine ⟨0,?_⟩
  rintro _ ⟨d,_,rfl⟩
  exact (ENNReal.toReal_nonneg : 0 ≤ iidWin 2 d (MeasureTheory.Measure.dirac 0)).trans
    (iidWin_le_extremal _ _ _)

theorem rightValue_le {c d : ℝ} (h : c<d) : rightValue c ≤ extremal 2 d :=
  csInf_le (rightSet_bdd c) ⟨d,h,rfl⟩

private theorem blocks_ne (c : ℝ) : (blockValues c).Nonempty := by
  let x (_ : Fin 1) := (1:ℝ)
  exact ⟨_,1,x,x,1,fun _ => zero_lt_one,⟨fun _ => zero_le_one,by simp [x]⟩,
    zero_lt_one,le_rfl,rfl⟩

theorem block_le_rightValue {c v : ℝ} (hc : 0<c) (hv : v ∈ blockValues c) :
    v≤rightValue c := by
  rcases hv with ⟨n,x,w,t,hx,hw,ht,ht1,rfl⟩
  apply le_csInf (rightSet_ne c)
  rintro _ ⟨d,hd,rfl⟩
  exact closedBlock_le_right hc hd ht ht1 x w hx hw

private theorem cap_of_bounds {c U : ℝ} (bounds : ∀ v ∈ blockValues c, v≤U) :
    CountCap c U := by
  classical
  intro N T x hT hx l
  let m := Fintype.card (↥T)
  let e := (Fintype.equivFin (↥T)).symm
  let a (i : Fin m) : Fin N := (e i : Fin N)
  have ma : m=T.card := Fintype.card_coe _
  have hmnat : 0<m := by rw [ma]; exact hT.card_pos
  have hM : (0:ℝ)<m := by exact_mod_cast hmnat
  let w (_ : Fin m) := 1/(m:ℝ)
  have hw : Mass w := ⟨fun _ => by dsimp [w]; positivity,by simp [w,hM.ne']⟩
  have sumlab (f : Fin N → ℝ) : ∑ i : Fin m,f (a i) = ∑ i ∈ T,f i :=
    (Equiv.sum_comp e (fun j : T => f j)).trans (Finset.sum_subtype T (fun _ => Iff.rfl) f).symm
  let b := triples T (fun i j k => x i+x j≤c*x k)
  let q := pairs T (fun i k => x i≤c*x k)
  have B : closedScore c (x ∘ a) w = b/(m:ℝ)^3 := by
    have per (i j k : Fin m) :
        (if x (a i)+x (a j)≤c*x (a k) then w i*w j*w k else 0) =
        (if x (a i)+x (a j)≤c*x (a k) then (1:ℝ) else 0)/(m:ℝ)^3 := by
      dsimp [w]; split_ifs <;> ring
    unfold closedScore
    simp only [Function.comp_apply,per,← Finset.sum_div]
    congr 1
    rw [show b = _ from triples_eq T (fun i j k => x i+x j≤c*x k)]
    let K (i j k : Fin N) := if x i+x j≤c*x k then (1:ℝ) else 0
    calc
      _ = ∑ i : Fin m, ∑ j : Fin m, ∑ k ∈ T, K (a i) (a j) k := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        exact sumlab (K (a i) (a j))
      _ = ∑ i : Fin m, ∑ j ∈ T, ∑ k ∈ T, K (a i) j k := by
        apply Finset.sum_congr rfl; intro i _
        exact sumlab (fun j => ∑ k ∈ T, K (a i) j k)
      _ = _ := sumlab (fun i => ∑ j ∈ T, ∑ k ∈ T,K i j k)
  have Q : closedPairs c (x ∘ a) w = q/(m:ℝ)^2 := by
    have per (i k : Fin m) :
        (if x (a i)≤c*x (a k) then w i*w k else 0) =
        (if x (a i)≤c*x (a k) then (1:ℝ) else 0)/(m:ℝ)^2 := by
      dsimp [w]; split_ifs <;> ring
    unfold closedPairs
    simp only [Function.comp_apply,per,← Finset.sum_div]
    congr 1
    rw [show q = _ from pairs_eq T (fun i k => x i≤c*x k)]
    let K (i k : Fin N) := if x i≤c*x k then (1:ℝ) else 0
    calc
      _ = ∑ i : Fin m, ∑ k ∈ T,K (a i) k := by
        apply Finset.sum_congr rfl; intro i _
        exact sumlab (K (a i))
      _ = _ := sumlab (fun i => ∑ k ∈ T,K i k)
  let r := (l:ℝ)/m
  have hr : 0≤r := by dsimp [r]; positivity
  have h := bounds _ (show blockValue (1/(1+r)) (closedScore c (x ∘ a) w)
      (closedPairs c (x ∘ a) w) ∈ blockValues c from
    ⟨m,x ∘ a,w,1/(1+r),fun i => hx _ (e i).property,hw,by positivity,
      (div_le_one (by linarith)).2 (by linarith),rfl⟩)
  rw [blockValue_odds _ _ hr,B,Q] at h
  have hp : 0<1+3*r+3*r^2 := by positivity
  have h' := (div_le_iff₀ hp).1 h
  change b+2*(l:ℝ)*q+(l:ℝ)^2*(T.card:ℝ) ≤ _
  rw [← ma]
  calc
    _ = (b/(m:ℝ)^3+2*r*(q/(m:ℝ)^2)+r^2)*(m:ℝ)^3 := by dsimp [r]; field_simp; ring
    _ ≤ U*(1+3*r+3*r^2)*(m:ℝ)^3 := mul_le_mul_of_nonneg_right h' (pow_nonneg hM.le 3)
    _ = _ := by dsimp [r]; field_simp; ring

/-- The population right limit bounds every uniform positive block with any
integer number of lower labels. -/
theorem countCap_rightValue {c : ℝ} (hc : 0<c) : CountCap c (rightValue c) :=
  cap_of_bounds (fun _ h => block_le_rightValue hc h)

/-- The right-hand limit of the unrestricted Borel supremum is determined
exactly by finite weak triple and pair probabilities at the endpoint. -/
theorem unrestricted_right_formula {c : ℝ} (hc : 0<c) :
    rightValue c = sSup (blockValues c) := by
  have bd : BddAbove (blockValues c) := ⟨rightValue c,fun _ h => block_le_rightValue hc h⟩
  apply le_antisymm
  · exact right_upper_of_countCap (cap_of_bounds (fun _ hb => le_csSup bd hb)) (fun _ => rightValue_le)
  · exact csSup_le (blocks_ne c) (fun _ hb => block_le_rightValue hc hb)

/-- A true jump for the unrestricted profile has a single finite witness at c. -/
theorem unrestricted_jump_iff_block {c : ℝ} (hc : 0<c) :
    (∃ J : ℝ, 0<J ∧ RightJump (extremal 2) c J) ↔
      ∃ v ∈ blockValues c, extremal 2 c<v := by
  constructor
  · rintro ⟨J,hJ,hjump⟩
    have lo : extremal 2 c+J≤rightValue c := by
      apply le_csInf (rightSet_ne c)
      rintro _ ⟨d,hd,rfl⟩
      exact hjump _ hd
    have hi : extremal 2 c<sSup (blockValues c) := by rw [← unrestricted_right_formula hc]; linarith
    exact (lt_csSup_iff ⟨rightValue c,fun _ h => block_le_rightValue hc h⟩ (blocks_ne c)).1 hi
  · rintro ⟨v,hv,he⟩
    refine ⟨v-extremal 2 c,sub_pos.mpr he,fun d hd => ?_⟩
    have h := (block_le_rightValue hc hv).trans (rightValue_le hd)
    linarith
#print axioms unrestricted_right_formula
#print axioms unrestricted_jump_iff_block
end ClosedSpectrum
