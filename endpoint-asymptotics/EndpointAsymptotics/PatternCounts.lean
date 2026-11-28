import Mathlib.Tactic

open Finset
open scoped BigOperators
noncomputable section
namespace ClosedSpectrum

private def bit (p : Prop) : ℝ := by
  classical exact if p then 1 else 0

private def box {α : Type*} (a b d : Finset α) (f : α → α → α → ℝ) : ℝ :=
  ∑ i ∈ a, ∑ j ∈ b, ∑ k ∈ d, f i j k

/-- The number of ordered triples from a finite set satisfying a predicate. -/
def triples {α : Type*} (s : Finset α) (H : α → α → α → Prop) : ℝ :=
  box s s s (fun i j k => bit (H i j k))

/-- The number of ordered pairs from a finite set satisfying a predicate. -/
def pairs {α : Type*} (s : Finset α) (Q : α → α → Prop) : ℝ :=
  ∑ i ∈ s, ∑ k ∈ s, bit (Q i k)

theorem triples_eq {α : Type*} (s : Finset α) (H : α → α → α → Prop)
    [∀ i j k, Decidable (H i j k)] : triples s H =
    ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, if H i j k then (1:ℝ) else 0 := by
  unfold triples box
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  apply sum_congr rfl; intro k _
  by_cases h : H i j k <;> simp [bit,h]

theorem pairs_eq {α : Type*} (s : Finset α) (H : α → α → Prop)
    [∀ i k, Decidable (H i k)] : pairs s H =
    ∑ i ∈ s, ∑ k ∈ s, if H i k then (1:ℝ) else 0 := by
  unfold pairs
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro k _
  by_cases h : H i k <;> simp [bit,h]

def zeros {α : Type*} (s : Finset α) (u : α → ℝ) : Finset α :=
  s.filter fun i => u i = 0

def positive {α : Type*} (s : Finset α) (u : α → ℝ) : Finset α :=
  s.filter fun i => 0 < u i

private theorem bit_mono {p q : Prop} (hpq : p → q) : bit p ≤ bit q := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp_all [bit]

private theorem box_mono {α : Type*} {a b d : Finset α} {f g : α → α → α → ℝ}
    (h : ∀ i ∈ a, ∀ j ∈ b, ∀ k ∈ d, f i j k ≤ g i j k) :
    box a b d f ≤ box a b d g :=
  sum_le_sum fun i hi => sum_le_sum fun j hj => sum_le_sum fun k hk => h i hi j hj k hk

private theorem box_vanishes {α : Type*} {a b d : Finset α} {H : α → α → α → Prop}
    (neg : ∀ i ∈ a, ∀ j ∈ b, ∀ k ∈ d, ¬ H i j k) :
    box a b d (fun i j k => bit (H i j k)) ≤ 0 := by
  calc
    _ ≤ box a b d (fun _ _ _ => 0) := box_mono (by
      intro i hi j hj k hk
      simp [bit,neg i hi j hj k hk])
    _ = 0 := by simp [box]

/-- Splitting a limit configuration into zero and positive labels. Only the
all-zero triples retain the original predicate without gaining an upper bound
from the nontrivial limit coordinates. -/
theorem partition_count_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (u : α → ℝ) (c : ℝ) (H : α → α → α → Prop)
    (hu : ∀ i ∈ s, 0 ≤ u i)
    (hweak : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, H i j k → u i + u j ≤ c*u k) :
    triples s H ≤ triples (zeros s u) H +
      triples (positive s u) (fun i j k => u i + u j ≤ c*u k) +
      2*((zeros s u).card : ℝ)*pairs (positive s u) (fun i k => u i ≤ c*u k) +
      ((zeros s u).card : ℝ)^2*((positive s u).card : ℝ) := by
  classical
  let L := zeros s u
  let T := positive s u
  let f := fun i j k => bit (H i j k)
  let Q := fun i k => u i ≤ c*u k
  have low {i} (hi : i ∈ L) : i ∈ s ∧ u i = 0 := mem_filter.mp hi
  have top {i} (hi : i ∈ T) : i ∈ s ∧ 0 < u i := mem_filter.mp hi
  have disj : Disjoint L T := by
    apply disjoint_left.mpr
    intro i hi ht
    linarith [(low hi).2,(top ht).2]
  have splitSet : s = L ∪ T := by
    ext i
    constructor
    · intro hi
      by_cases hzero : u i = 0
      · exact mem_union_left T (mem_filter.mpr ⟨hi,hzero⟩)
      · exact mem_union_right L (mem_filter.mpr ⟨hi,lt_of_le_of_ne (hu i hi) (Ne.symm hzero)⟩)
    · intro hi
      rcases mem_union.mp hi with hi|hi
      · exact (low hi).1
      · exact (top hi).1
  have decomposition : box s s s f =
      box L L L f + box L L T f + box L T L f + box L T T f +
      box T L L f + box T L T f + box T T L f + box T T T f := by
    conv_lhs => rw [splitSet]
    simp only [box,sum_union disj,sum_add_distrib]
    ring
  have ltl : box L T L f ≤ 0 := by
    apply box_vanishes
    intro i hi j hj k hk hwin
    have h := hweak _ (low hi).1 _ (top hj).1 _ (low hk).1 hwin
    rw [(low hi).2,(low hk).2] at h
    linarith [(top hj).2]
  have tll : box T L L f ≤ 0 := by
    apply box_vanishes
    intro i hi j hj k hk hwin
    have h := hweak _ (top hi).1 _ (low hj).1 _ (low hk).1 hwin
    rw [(low hj).2,(low hk).2] at h
    linarith [(top hi).2]
  have ttl : box T T L f ≤ 0 := by
    apply box_vanishes
    intro i hi j hj k hk hwin
    have h := hweak _ (top hi).1 _ (top hj).1 _ (low hk).1 hwin
    rw [(low hk).2] at h
    linarith [(top hi).2,(top hj).2]
  have llt : box L L T f ≤ (L.card:ℝ)^2*(T.card:ℝ) := by
    calc
      _ ≤ box L L T (fun _ _ _ => 1) := box_mono (by
        intro i _ j _ k _
        dsimp [f,bit]
        split_ifs <;> norm_num)
      _ = _ := by simp [box,nsmul_eq_mul]; ring
  have ltt : box L T T f ≤ (L.card:ℝ)*pairs T Q := by
    calc
      _ ≤ box L T T (fun _ j k => bit (Q j k)) := box_mono (by
        intro i hi j hj k hk
        apply bit_mono
        intro hwin
        have h := hweak _ (low hi).1 _ (top hj).1 _ (top hk).1 hwin
        simpa [Q,(low hi).2] using h)
      _ = _ := by simp [box,pairs,nsmul_eq_mul]
  have tlt : box T L T f ≤ (L.card:ℝ)*pairs T Q := by
    calc
      _ ≤ box T L T (fun i _ k => bit (Q i k)) := box_mono (by
        intro i hi j hj k hk
        apply bit_mono
        intro hwin
        have h := hweak _ (top hi).1 _ (low hj).1 _ (top hk).1 hwin
        simpa [Q,(low hj).2] using h)
      _ = _ := by simp [box,pairs,nsmul_eq_mul,← Finset.mul_sum]
  have ttt : box T T T f ≤ triples T (fun i j k => u i+u j≤c*u k) := by
    apply box_mono
    intro i hi j hj k hk
    exact bit_mono (hweak _ (top hi).1 _ (top hj).1 _ (top hk).1)
  change box s s s f ≤ box L L L f + triples T (fun i j k => u i+u j≤c*u k) +
    2*(L.card:ℝ)*pairs T Q + (L.card:ℝ)^2*(T.card:ℝ)
  rw [decomposition]
  linarith

#print axioms partition_count_bound
end ClosedSpectrum
