import EmpiricalLaw
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators
open IidJumpSpectra

namespace IidInfiniteJumps

/-- A translated geometric progression with bottom entry zero. -/
noncomputable def ladder (c : ℝ) (i : ℕ) := 1 - (c⁻¹) ^ i

theorem ladder_nonneg {c : ℝ} (hc : 1 < c) (i : ℕ) : 0 ≤ ladder c i := by
  have hc' : 0 < c := by linarith
  exact sub_nonneg.mpr (pow_le_one₀ (inv_nonneg.mpr hc'.le)
    (inv_le_one_of_one_le₀ hc.le))

theorem ladder_mono {c : ℝ} (hc : 1 < c) : Monotone (ladder c) := by
  intro i j hij
  apply sub_le_sub_left
  exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hc.le) hij

theorem ladder_succ {c : ℝ} (hc : 1 < c) (i : ℕ) :
    c * ladder c (i + 1) = ladder c i + (c-1) := by
  have hc' : c ≠ 0 := by linarith
  simp only [ladder, pow_succ]
  field_simp
  ring

theorem ladder_compare {n : ℕ} {c : ℝ} (hc : 1 < c) (hc' : c ≤ 2)
    (h : 2-c < (c⁻¹) ^ n) (i j k : Fin (n+1)) :
    ladder c i.val + ladder c j.val < c * ladder c k.val ↔ i < k ∨ j < k := by
  have bound (x : Fin (n+1)) : ladder c x.val < c-1 := by
    have hu := ladder_mono hc (show x.val ≤ n by omega)
    have : ladder c n < c-1 := by dsimp [ladder]; linarith
    exact hu.trans_lt this
  have suffices_one (u v : Fin (n+1)) (hu : u < k) :
      ladder c u.val + ladder c v.val < c * ladder c k.val := by
    have step := ladder_succ hc u.val
    have mono := ladder_mono hc (show u.val+1 ≤ k.val from hu)
    have mono' := mul_le_mul_of_nonneg_left mono (show 0 ≤ c by linarith)
    linarith [bound v]
  constructor
  · contrapose!
    rintro ⟨hi, hj⟩
    have hL := ladder_nonneg hc k.val
    have hC := mul_le_mul_of_nonneg_right hc' hL
    linarith [ladder_mono hc (show k.val ≤ i.val from hi),
      ladder_mono hc (show k.val ≤ j.val from hj)]
  · rintro (h1 | h2)
    · exact suffices_one i j h1
    · simpa [add_comm] using suffices_one j i h2


private theorem sum_tail_sq (N : ℕ) :
    (∑ i : Fin N, ((N : ℝ) - i.val)^2) =
      (N : ℝ) * (N+1) * (2*N+1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, sub_zero, Fin.val_succ, Nat.cast_add,
      Nat.cast_one, Nat.cast_succ]
    simp_rw [show ∀ i : Fin N, ((N : ℝ)+1) - ((i.val : ℝ)+1) = N-i.val by intro i; ring]
    rw [ih]
    ring

private theorem rank_indicators {N : ℕ} (k : Fin N) :
    (∑ i : Fin N, (if k ≤ i then 1 else 0 : ℝ)) = N-k.val := by
  rw [Finset.sum_boole]
  have h : (Finset.univ.filter (fun i : Fin N => k ≤ i)) = Finset.Ici k := by
    ext i; simp
  rw [h, Fin.card_Ici, Nat.cast_sub (by omega : k.val ≤ N)]

private theorem pair_count {N : ℕ} (k : Fin N) :
    (∑ f : (Fin 2 → Fin N), (if f 0 < k ∨ f 1 < k then 1 else 0 : ℝ)) =
      (N : ℝ)^2 - (N-k.val)^2 := by
  classical
  let u (i : Fin N) : ℝ := if k ≤ i then 1 else 0
  have per (i j : Fin N) : (if i < k ∨ j < k then 1 else 0 : ℝ) =
      1-u i*u j := by
    dsimp [u]
    by_cases ha : i < k <;> by_cases hb : j < k <;>
      simp [ha, hb, not_le_of_gt, le_of_not_gt, *]
  let g (p : Fin N × Fin N) : ℝ := 1-u p.1*u p.2
  calc
    _ = ∑ f : Fin 2 → Fin N, g (finTwoArrowEquiv (Fin N) f) := by
      apply Finset.sum_congr rfl
      intro f _
      exact per _ _
    _ = ∑ p, g p := Equiv.sum_comp _ _
    _ = (N : ℝ)^2 - (N-k.val)^2 := by
      rw [Fintype.sum_prod_type]
      dsimp [g]
      simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      have hu : (∑ i : Fin N, u i) = (N:ℝ)-k.val := rank_indicators k
      simp only [hu, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one, pow_two]

theorem ladder_frequency {n : ℕ} {c : ℝ} (hc : 1 < c) (hc' : c ≤ 2)
    (h : 2-c < (c⁻¹) ^ n) :
    frequency (winsSet (m := 2) (fun i : Fin (n+1) => ladder c i.val) c) =
      2/3 - 1/(2*(n+1 : ℝ)) - 1/(6*(n+1 : ℝ)^2) := by
  classical
  let N := n+1
  let v (i : Fin N) := ladder c i.val
  have count : ((winsSet (m := 2) v c).card : ℝ) =
      ∑ k : Fin N, ((N:ℝ)^2 - (N-k.val)^2) := by
    unfold winsSet
    rw [Finset.card_filter]
    push_cast
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← pair_count]
    apply Finset.sum_congr rfl
    intro f _
    have hw : wins v c (f,k) ↔ f 0 < k ∨ f 1 < k := by
      simpa [wins, Fin.sum_univ_two, v] using ladder_compare hc hc' h (f 0) (f 1) k
    by_cases hwin : wins v c (f,k) <;> simp [hw, hwin, *] at *
  change ((winsSet (m := 2) v c).card : ℝ) / (N:ℝ)^3 = _
  rw [count, Finset.sum_sub_distrib, sum_tail_sq]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, N, Nat.cast_succ]
  have hN : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem lower_bound {n : ℕ} {c : ℝ} (hc : 1 < c) (hc' : c ≤ 2)
    (h : 2-c < (c⁻¹) ^ n) :
    2/3 - 1/(2*(n+1 : ℝ)) - 1/(6*(n+1 : ℝ)^2) ≤ extremal 2 c := by
  rw [← ladder_frequency hc hc' h]
  exact frequency_le_extremal _ (fun i => ladder_nonneg hc i.val) c

#print axioms lower_bound
end IidInfiniteJumps
