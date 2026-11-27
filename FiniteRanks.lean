import EmpiricalLaw
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

open Finset
open scoped BigOperators
open IidJumpSpectra
noncomputable section

namespace IidStaircase

def rankCut (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 + rankCut c n) / c

private lemma covers {c z y : ℝ} (hy : 0 ≤ y) :
    ∀ (m : ℕ), 0 < m → y ≤ rankCut c m * z →
    ∃ j : Fin m, rankCut c j.val * z ≤ y ∧ y ≤ rankCut c (j.val + 1) * z := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
    intro _ hlast
    by_cases h : 0 < m ∧ y ≤ rankCut c m * z
    · obtain ⟨j, hj⟩ := ih h.1 h.2
      exact ⟨j.castSucc, hj⟩
    · refine ⟨Fin.last m, ?_, hlast⟩
      change rankCut c m * z ≤ y
      by_cases hm : m = 0
      · simpa [hm, rankCut] using hy
      · exact (lt_of_not_ge (fun hl => h ⟨Nat.pos_of_ne_zero hm, hl⟩)).le

private def bit (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

private lemma bit_nonneg (P : Prop) [Decidable P] : 0 ≤ bit P := by
  unfold bit
  split <;> norm_num

private lemma bit_le (P : Prop) [Decidable P] : bit P ≤ 1 := by
  unfold bit
  split <;> norm_num

private def wins3 {N : ℕ} (x : Fin N → ℝ) (c : ℝ) (i j k : Fin N) : ℝ :=
  bit (x i + x j < c * x k)

private def rankScore {N m : ℕ} (col : Fin N → Fin N → Fin m) (k i j : Fin N) : ℝ :=
  if i ≤ k ∧ j ≤ k then if col k i = col k j then 1 else 2 else 0

private lemma rankScore_nonneg {N m} (col : Fin N → Fin N → Fin m) (k i j : Fin N) :
    0 ≤ rankScore col k i j := by
  simp only [rankScore]
  split_ifs <;> norm_num

private lemma upper_at_max {N m : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hxmono : Monotone x) {c : ℝ} (hc2 : c ≤ 2) (col : Fin N → Fin N → Fin m)
    (hsame : ∀ k i j, i ≤ k → j ≤ k → col k i = col k j → c * x j ≤ x k + x i)
    (k i j : Fin N) (hi : i ≤ k) (hj : j ≤ k) :
    wins3 x c i j k + wins3 x c j k i + wins3 x c k i j ≤ rankScore col k i j := by
  have ht := bit_le (x i + x j < c * x k)
  have hu := bit_le (x j + x k < c * x i)
  have hv := bit_le (x k + x i < c * x j)
  simp only [rankScore, if_pos (And.intro hi hj), wins3]
  by_cases hcol : col k i = col k j
  · have h1 := hsame k i j hi hj hcol
    have h2 := hsame k j i hj hi hcol.symm
    simp only [if_pos hcol, bit, if_neg (not_lt_of_ge h1),
      if_neg (not_lt_of_ge (by linarith : c * x i ≤ x j + x k)), add_zero]
    exact ht
  · rw [if_neg hcol]
    rcases le_total i j with hij | hji
    · have h1 := mul_le_mul_of_nonneg_right hc2 (hx i)
      have h2 := hxmono hij
      have h3 := hxmono hi
      have hno : ¬ x j + x k < c * x i := by linarith
      simp only [bit, if_neg hno, add_zero] at *
      linarith
    · have h1 := mul_le_mul_of_nonneg_right hc2 (hx j)
      have h2 := hxmono hji
      have h3 := hxmono hj
      have hno : ¬ x k + x i < c * x j := by linarith
      simp only [bit, if_neg hno, add_zero] at *
      linarith

private lemma total_pointwise {N m : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hxmono : Monotone x) {c : ℝ} (hc2 : c ≤ 2) (col : Fin N → Fin N → Fin m)
    (hsame : ∀ k i j, i ≤ k → j ≤ k → col k i = col k j → c * x j ≤ x k + x i)
    (i j k : Fin N) :
    wins3 x c i j k + wins3 x c j k i + wins3 x c k i j ≤
    rankScore col k i j + rankScore col i j k + rankScore col j k i := by
  have hn1 := rankScore_nonneg col k i j
  have hn2 := rankScore_nonneg col i j k
  have hn3 := rankScore_nonneg col j k i
  rcases le_total i j with hij | hji
  · rcases le_total j k with hjk | hkj
    · linarith [upper_at_max x hx hxmono hc2 col hsame k i j (hij.trans hjk) hjk]
    · linarith [upper_at_max x hx hxmono hc2 col hsame j k i hkj hij]
  · rcases le_total i k with hik | hki
    · linarith [upper_at_max x hx hxmono hc2 col hsame k i j hik (hji.trans hik)]
    · linarith [upper_at_max x hx hxmono hc2 col hsame i j k hji hki]

private lemma exists_colors {N m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    (hcut : 1 ≤ rankCut c m) (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) (hxmono : Monotone x) :
    ∃ col : Fin N → Fin N → Fin m, ∀ k i j, i ≤ k → j ≤ k → col k i = col k j →
      c * x j ≤ x k + x i := by
  classical
  have h (k i : Fin N) : ∃ b : Fin m, i ≤ k →
      rankCut c b.val * x k ≤ x i ∧ x i ≤ rankCut c (b.val+1) * x k := by
    by_cases hik : i ≤ k
    · have ht := mul_le_mul_of_nonneg_right hcut (hx k)
      obtain ⟨b, hb⟩ := covers (c := c) (z := x k) (hx i) m hm
        ((hxmono hik).trans (by simpa using ht))
      exact ⟨b, fun _ => hb⟩
    · exact ⟨⟨0,hm⟩, fun h' => (hik h').elim⟩
  choose col hcol using h
  refine ⟨col, ?_⟩
  intro k i j hi hj heq
  have h1 := (hcol k i hi).1
  have h2 := (hcol k j hj).2
  rw [← heq, rankCut] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hc.le
  field_simp [hc.ne'] at h3
  nlinarith

private lemma rotation {N : ℕ} (f : Fin N → Fin N → Fin N → ℝ) :
    (∑ i, ∑ j, ∑ k, f j k i) = ∑ i, ∑ j, ∑ k, f i j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

private lemma symmetric_totals {N : ℕ} (f : Fin N → Fin N → Fin N → ℝ) :
    (∑ i, ∑ j, ∑ k, (f i j k + f j k i + f k i j)) =
    3 * ∑ i, ∑ j, ∑ k, f i j k := by
  simp only [Finset.sum_add_distrib]
  have h := rotation (fun i j k => f k i j)
  simp only at h
  rw [rotation f, ← h]
  ring

private lemma equal_pairs {N m : ℕ} (s : Finset (Fin N)) (f : Fin N → Fin m) :
    (∑ i ∈ s, ∑ j ∈ s, bit (f i = f j)) =
    ∑ b : Fin m, (∑ i ∈ s, bit (f i = b)) ^ 2 := by
  classical
  have h (i j : Fin N) : bit (f i = f j) =
      ∑ b : Fin m, bit (f i = b) * bit (f j = b) := by
    simp [bit, ite_mul, eq_comm]
  simp_rw [h]
  simp_rw [Finset.sum_comm (s := s) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro b _
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

private lemma one_max_total {N m : ℕ} (hm : 0 < m)
    (col : Fin N → Fin N → Fin m) (k : Fin N) :
    (∑ i, ∑ j, rankScore col k i j) ≤
    (2 - 1 / (m : ℝ)) * ((k.val : ℝ) + 1) ^ 2 := by
  classical
  let s := Finset.Iic k
  let n (b : Fin m) := ∑ i ∈ s, bit (col k i = b)
  have hsum : (∑ b, n b) = (s.card : ℝ) := by
    dsimp [n]
    rw [Finset.sum_comm]
    simp [bit]
  have hh : (∑ i, ∑ j, rankScore col k i j) =
      ∑ i ∈ s, ∑ j ∈ s, (2 - bit (col k i = col k j)) := by
    have heq (i j : Fin N) : rankScore col k i j = if i ∈ s then
        (if j ∈ s then 2 - bit (col k i = col k j) else 0) else 0 := by
      simp only [s, Finset.mem_Iic, rankScore, bit]
      by_cases h1 : i ≤ k <;> by_cases h2 : j ≤ k <;> by_cases h3 : col k i = col k j <;> norm_num [h1,h2,h3]
    simp_rw [heq]
    simp [Finset.sum_ite_irrel]
  have hcs : ((s.card : ℝ)) ^ 2 ≤ (m : ℝ) * ∑ b, n b ^ 2 := by
    have hcs' := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m))) (f := n)
    simpa [hsum] using hcs'
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have ha : (s.card : ℝ)^2 / m ≤ ∑ b, n b ^ 2 := by
    apply (div_le_iff₀ hm').2
    linarith
  rw [hh]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [equal_pairs, show (s.card : ℝ) = (k.val : ℝ)+1 by simp [s, Fin.card_Iic]]
  dsimp [n] at ha
  rw [show (s.card : ℝ) = (k.val : ℝ)+1 by simp [s, Fin.card_Iic]] at ha
  linarith [show (1/(m:ℝ))*((k.val:ℝ)+1)^2 = ((k.val:ℝ)+1)^2/m by ring]

private lemma sorted_count {N m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    (hc2 : c ≤ 2) (hcut : 1 ≤ rankCut c m) (x : Fin N → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hxm : Monotone x) :
    (∑ i, ∑ j, ∑ k, wins3 x c i j k) ≤
    (2 - 1 / (m : ℝ)) * ∑ k : Fin N, ((k.val : ℝ)+1)^2 := by
  obtain ⟨col,hs⟩ := exists_colors hm hc hcut x hx hxm
  let g (i j k : Fin N) := rankScore col k i j
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => Finset.sum_le_sum (s := Finset.univ)
      (fun k _ => total_pointwise x hx hxm hc2 col hs i j k)))
  change (∑ i, ∑ j, ∑ k, (wins3 x c i j k + wins3 x c j k i + wins3 x c k i j)) ≤
      (∑ i, ∑ j, ∑ k, (g i j k + g j k i + g k i j)) at hp
  rw [symmetric_totals, symmetric_totals] at hp
  have hrot' := rotation g
  change (∑ i, ∑ j, ∑ k, rankScore col i j k) = _ at hrot'
  rw [← hrot'] at hp
  have hbound := Finset.sum_le_sum (s := Finset.univ) (fun k _ => one_max_total hm col k)
  rw [← Finset.mul_sum] at hbound
  linarith

private lemma squared_ranks (N : ℕ) :
    (∑ k : Fin N, ((k.val : ℝ)+1)^2) =
      (N : ℝ) * (N+1) * (2*N+1)/6 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ k : Fin N, ((k.val : ℝ)+1)^2) + ((N : ℝ)+1)^2 = _
    rw [ih]
    push_cast
    ring

private lemma sum_wins {N : ℕ} (x : Fin N → ℝ) (c : ℝ) :
    ((winsSet (m := 2) x c).card : ℝ) = ∑ i, ∑ j, ∑ k, wins3 x c i j k := by
  classical
  have h : ((winsSet (m := 2) x c).card : ℝ) =
      ∑ q : Comparison 2 N, bit (wins x c q) := by
    simp [winsSet, bit]
  rw [h, Fintype.sum_prod_type]
  let e := piFinTwoEquiv (fun _ : Fin 2 => Fin N)
  let f (p : Fin N × Fin N) := ∑ k, wins3 x c p.1 p.2 k
  have ht := e.sum_comp f
  change (∑ q : Fin 2 → Fin N, ∑ k, bit (wins x c (q,k))) = _
  have hf : ∀ q : Fin 2 → Fin N, (∑ k, bit (wins x c (q,k))) = f (e q) := by
    intro q
    simp [f, e, piFinTwoEquiv, wins3, wins, Fin.sum_univ_two]
  simp_rw [hf]
  rw [ht, Fintype.sum_prod_type]

private lemma reorder {N : ℕ} (x : Fin N → ℝ) (c : ℝ) (e : Equiv.Perm (Fin N)) :
    (∑ i, ∑ j, ∑ k, wins3 (x ∘ e) c i j k) = ∑ i, ∑ j, ∑ k, wins3 x c i j k := by
  change (∑ i, ∑ j, ∑ k, wins3 x c (e i) (e j) (e k)) = _
  have first (i j : Fin N) := Equiv.sum_comp e (wins3 x c i j)
  simp_rw [first]
  have second (i : Fin N) := Equiv.sum_comp e (fun j => ∑ k, wins3 x c i j k)
  simp_rw [second]
  exact Equiv.sum_comp e (fun i => ∑ j, ∑ k, wins3 x c i j k)

/-- A deterministic sample bound. Ranking the labels breaks ties in the
sample values; the count also includes draws with repeated labels. -/
theorem finite_upper {m N : ℕ} [NeZero N] (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    (hc2 : c ≤ 2) (hcut : 1 ≤ rankCut c m) (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) :
    frequency (winsSet (m := 2) x c) ≤
    (2 - 1 / (m : ℝ)) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / (6 * (N : ℝ)^2) := by
  let e := Tuple.sort x
  have h := sorted_count hm hc hc2 hcut (x ∘ e) (fun i => hx (e i)) (Tuple.monotone_sort x)
  rw [reorder, squared_ranks] at h
  have hn : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [frequency, sum_wins]
  apply (div_le_iff₀ (by positivity)).2
  convert h using 1
  field_simp [hn.ne']
  ring

#print axioms finite_upper
end IidStaircase
