import EndpointAsymptotics.FullRankWindow
import EndpointAsymptotics.ClosedBlockLower
import Mathlib.Data.Fin.Tuple.Sort

open Finset OneScale ClosedSpectrum
open scoped BigOperators
noncomputable section
namespace FullRankWindow

/-- Weight of the maximal possible winning pattern on a tuple in descending order. -/
def rankScore {m : ℕ} (w : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if k < i ∨ k < j then w i*w j*w k else 0

private theorem relabel {m : ℕ} (e : Equiv.Perm (Fin m)) (f : Fin m → Fin m → Fin m → ℝ) :
    (∑ i, ∑ j, ∑ k, f (e i) (e j) (e k)) = ∑ i, ∑ j, ∑ k, f i j k := by
  calc
    _ = ∑ i, ∑ j, ∑ k, f (e i) (e j) k := by
      apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro j _
      exact Equiv.sum_comp e (fun k => f (e i) (e j) k)
    _ = ∑ i, ∑ j, ∑ k, f (e i) j k := by
      apply sum_congr rfl; intro i _
      exact Equiv.sum_comp e (fun j => ∑ k, f (e i) j k)
    _ = _ := Equiv.sum_comp e (fun i => ∑ j, ∑ k, f i j k)

/-- Arbitrary relative scales and arbitrary weights on m positive labels are
dominated by the maximal rank polynomial after reordering those weights. -/
theorem sorted_dominance {m : ℕ} {c : ℝ} (hc : c < 2) (x w : Fin m → ℝ)
    (hx : ∀ i,0 < x i) (hw : Mass w) :
    ∃ e : Equiv.Perm (Fin m), Mass (w ∘ e) ∧ closedScore c x w ≤ rankScore (w ∘ e) := by
  classical
  let e := Tuple.sort (fun i => -x i)
  have anti : Antitone (x ∘ e) := by
    intro i j hij
    have h := Tuple.monotone_sort (fun i => -x i) hij
    change -x (e i) ≤ -x (e j) at h
    exact neg_le_neg_iff.mp h
  refine ⟨e,⟨fun i => hw.1 (e i),(Equiv.sum_comp e w).trans hw.2⟩,?_⟩
  let f (i j k : Fin m) : ℝ := if x i+x j ≤ c*x k then w i*w j*w k else 0
  have eq : closedScore c x w = ∑ i, ∑ j, ∑ k, f (e i) (e j) (e k) := (relabel e f).symm
  rw [eq]
  unfold rankScore
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
  by_cases h : x (e i)+x (e j) ≤ c*x (e k)
  · have ranks : k < i ∨ k < j := by
      by_contra! bad
      have u : x (e k) ≤ x (e i) := anti bad.1
      have v : x (e k) ≤ x (e j) := anti bad.2
      nlinarith only [u,v,h,mul_pos (sub_pos.mpr hc) (hx (e k))]
    simp [f,h,ranks]
  · by_cases ranks : k < i ∨ k < j
    · simpa [f,h,ranks,Function.comp_apply] using mul_nonneg (mul_nonneg (hw.1 (e i)) (hw.1 (e j))) (hw.1 (e k))
    · simp [f,h,ranks]

/-- Once the n+1-level window opens, the same positive support realizes the
universal upper rank polynomial simultaneously for every choice of weights.
The pair score equals one as well. -/
theorem sharp_rank_block {n : ℕ} {c : ℝ} (hc : 1 < c) (h2 : c < 2)
    (h : (2-c)*c^(n+1) ≤ 1) :
    ∃ y : Fin (n+1) → ℝ, (∀ i,0 < y i) ∧ ∀ w, Mass w →
      closedScore c y w = rankScore w ∧ closedPairs c y w=1 := by
  classical
  obtain ⟨x,_,hx,hp,ht⟩ := (weak_iff hc h2).2 h
  let y (i : Fin (n+1)) := x i.val
  have hi (i : Fin (n+1)) : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  refine ⟨y,fun i => hx _ (hi i),fun w hw => ⟨?_,?_⟩⟩
  · unfold closedScore rankScore
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    have hh : y i+y j ≤ c*y k ↔ k < i ∨ k < j := ht i.val (hi i) j.val (hi j) k.val (hi k)
    simp only [hh]
  · unfold closedPairs
    have ha (i k : Fin (n+1)) : y i ≤ c*y k := hp i.val (hi i) k.val (hi k)
    simp only [if_pos (ha _ _),←mul_sum,hw.2,mul_one]

/-- The fixed-cardinality optimum over arbitrary coordinates on the plateau
equals the optimum over weights of one coefficient-independent polynomial. -/
theorem rank_plateau {n : ℕ} {c : ℝ} (hc : 1 < c) (h2 : c < 2) (h : (2-c)*c^(n+1) ≤ 1) :
    ∀ u : ℝ,
      (∀ (x w : Fin (n+1) → ℝ), (∀ i,0 < x i) → Mass w → closedScore c x w ≤ u) ↔
      (∀ w : Fin (n+1) → ℝ, Mass w → rankScore w ≤ u) := by
  obtain ⟨y,hy,hwins⟩ := sharp_rank_block hc h2 h
  intro u
  constructor
  · intro cap w hw
    rw [←(hwins w hw).1]
    exact cap y w hy hw
  · intro cap x w hx hw
    obtain ⟨e,hw',hdom⟩ := sorted_dominance h2 x w hx hw
    exact hdom.trans (cap _ hw')

#print axioms sorted_dominance
#print axioms sharp_rank_block
#print axioms rank_plateau
end FullRankWindow
