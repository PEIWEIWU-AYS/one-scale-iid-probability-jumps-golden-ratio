import EndpointAsymptotics.RankInterior
import EndpointAsymptotics.FullRankTransfer
import Mathlib.Analysis.Convex.Topology

open Finset OneScale ClosedSpectrum Set
open scoped BigOperators
noncomputable section
namespace FullRankWindow

abbrev RankTables (m : ℕ) := (Fin m → Fin m → Fin m → Bool) × (Fin m → Fin m → Bool)

def tableTriple {m : ℕ} (P : RankTables m) (w : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if P.1 i j k then w i*w j*w k else 0

def tablePair {m : ℕ} (P : RankTables m) (w : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ k, if P.2 i k then w i*w k else 0

/-- Strict tables from all positive blocks with their coordinates put into
descending order and the largest entry normalized to one. -/
def strictFeasible {n : ℕ} (c : ℝ) (P : RankTables (n+1)) : Prop :=
  ∃ x : ℕ → ℝ, x 0=1 ∧ (∀ i≤n,0<x i) ∧ (∀ i≤n,∀ j≤n,i≤j → x j≤x i) ∧
    (∀ i j k : Fin (n+1), P.1 i j k=true ↔ x i.val+x j.val<c*x k.val) ∧
    (∀ i k : Fin (n+1), P.2 i k=true ↔ x i.val<c*x k.val)

private theorem strict_sum3 {m : ℕ} {f g : Fin m → Fin m → Fin m → ℝ}
    (hle : ∀ i j k, f i j k ≤ g i j k) {i j k : Fin m} (hlt : f i j k<g i j k) :
    (∑ a, ∑ b, ∑ d, f a b d)<∑ a, ∑ b, ∑ d, g a b d := by
  apply sum_lt_sum (fun a _ => sum_le_sum fun b _ => sum_le_sum fun d _ => hle a b d)
  refine ⟨i,mem_univ _,?_⟩
  apply sum_lt_sum (fun b _ => sum_le_sum fun d _ => hle i b d)
  exact ⟨j,mem_univ _,sum_lt_sum (fun d _ => hle _ _ d) ⟨k,mem_univ _,hlt⟩⟩

private theorem strict_sum2 {m : ℕ} {f g : Fin m → Fin m → ℝ}
    (hle : ∀ i j, f i j ≤ g i j) {i j : Fin m} (hlt : f i j<g i j) :
    (∑ a, ∑ b, f a b)<∑ a, ∑ b, g a b := by
  apply sum_lt_sum (fun a _ => sum_le_sum fun b _ => hle a b)
  exact ⟨i,mem_univ _,sum_lt_sum (fun b _ => hle _ b) ⟨j,mem_univ _,hlt⟩⟩

theorem table_caps {n : ℕ} {c : ℝ} (h2 : c<2) {P : RankTables (n+1)}
    (fe : strictFeasible c P) (w : Fin (n+1) → ℝ) (hw : Mass w) :
    tableTriple P w≤rankScore w ∧ tablePair P w≤1 := by
  classical
  obtain ⟨x,_,hx,mono,tr,_⟩ := fe
  have rank (i j k : Fin (n+1)) (hit : P.1 i j k=true) : k < i ∨ k < j := by
    by_contra! bad
    have raw := (tr i j k).1 hit
    have a := mono i.val (by omega) k.val (by omega) bad.1
    have b := mono j.val (by omega) k.val (by omega) bad.2
    nlinarith only [raw,a,b,mul_pos (sub_pos.mpr h2) (hx k.val (by omega))]
  constructor
  · unfold tableTriple rankScore
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
    by_cases hit : P.1 i j k=true
    · simp [hit,rank i j k hit]
    · simp only [if_neg hit]; split_ifs
      · exact mul_nonneg (mul_nonneg (hw.1 _) (hw.1 _)) (hw.1 _)
      · exact le_rfl
  · unfold tablePair
    calc
      _ ≤ ∑ i, ∑ k, w i*w k := by
        apply sum_le_sum;intro i _
        apply sum_le_sum;intro k _
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hw.1 _) (hw.1 _)
      _ = 1 := by simp only [←mul_sum,hw.2,mul_one]

/-- At the exact threshold not even a single strict table and any choice of
weights can saturate both separate upper bounds. -/
theorem strict_table_misses {n : ℕ} {c : ℝ} (hc : 1<c) (h2 : c<2)
    (root : (2-c)*c^(n+1)=1) {P : RankTables (n+1)} (fe : strictFeasible c P)
    (w : Fin (n+1) → ℝ) (hw : Mass w) :
    tableTriple P w<peak n ∨ tablePair P w<1 := by
  classical
  by_contra! both
  have caps := table_caps h2 fe w hw
  have eqrank := le_antisymm ((rank_peak n).2 w hw) (both.1.trans caps.1)
  have eqtr := le_antisymm caps.1 (eqrank ▸ both.1)
  have eqpa := le_antisymm caps.2 both.2
  have pos := optimal_weights_positive w hw eqrank
  obtain ⟨x,h0,hx,mono,xt,xp⟩ := fe
  have rank (i j k : Fin (n+1)) (hit : P.1 i j k=true) : k < i ∨ k < j := by
    by_contra! bad
    have raw := (xt i j k).1 hit
    have a := mono i.val (by omega) k.val (by omega) bad.1
    have b := mono j.val (by omega) k.val (by omega) bad.2
    nlinarith only [raw,a,b,mul_pos (sub_pos.mpr h2) (hx k.val (by omega))]
  have completeT (i j k : Fin (n+1)) (target : k < i ∨ k < j) : P.1 i j k=true := by
    by_contra miss
    let f (i j k : Fin (n+1)) := if P.1 i j k then w i*w j*w k else 0
    let g (i j k : Fin (n+1)) := if k < i ∨ k < j then w i*w j*w k else 0
    have dom (u v z) : f u v z≤g u v z := by
      by_cases hit : P.1 u v z=true
      · simp [f,g,hit,rank _ _ _ hit]
      · dsimp [f,g];rw [if_neg hit];split_ifs
        · exact (mul_pos (mul_pos (pos u) (pos v)) (pos z)).le
        · exact le_rfl
    have gap : f i j k<g i j k := by
      simp only [f,g,if_neg miss,if_pos target]
      exact mul_pos (mul_pos (pos i) (pos j)) (pos k)
    exact eqtr.not_lt (strict_sum3 dom gap)
  have completeP (i k : Fin (n+1)) : P.2 i k=true := by
    by_contra miss
    let f (u v : Fin (n+1)) := if P.2 u v then w u*w v else 0
    have dom (u v) : f u v≤w u*w v := by
      dsimp [f]; split_ifs
      · exact le_rfl
      · exact (mul_pos (pos u) (pos v)).le
    have gap : f i k<w i*w k := by simpa [f,miss] using mul_pos (pos i) (pos k)
    have less := strict_sum2 dom gap
    change tablePair P w < ∑ u, ∑ v, w u*w v at less
    simp only [←mul_sum,hw.2,mul_one] at less
    exact eqpa.not_lt less
  have all : Realizes (· < ·) n c := by
    refine ⟨x,h0,hx,?_,?_⟩
    · intro i hi k hk
      let I : Fin (n+1) := ⟨i,by omega⟩
      let K : Fin (n+1) := ⟨k,by omega⟩
      exact (xp I K).mp (completeP I K)
    · intro i hi j hj k hk
      let I : Fin (n+1) := ⟨i,by omega⟩
      let J : Fin (n+1) := ⟨j,by omega⟩
      let K : Fin (n+1) := ⟨k,by omega⟩
      exact ⟨fun h => rank I J K ((xt I J K).2 h),
        fun h => (xt I J K).1 (completeT I J K h)⟩
  exact root.not_lt ((strict_iff hc h2).mp all)

#print axioms strict_table_misses
end FullRankWindow
