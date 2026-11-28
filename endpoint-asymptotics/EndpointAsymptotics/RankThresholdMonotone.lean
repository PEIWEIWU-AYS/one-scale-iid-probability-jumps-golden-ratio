import EndpointAsymptotics.FullRankWindow
import Mathlib.Algebra.GeomSum

open Finset
noncomputable section
namespace FullRankWindow

private def reciprocalSum (m : ℕ) (c : ℝ) := ∑ j ∈ range m, (c⁻¹)^(j+1)

private theorem window_identity {c : ℝ} (hc : 0<c) (m : ℕ) :
    (c-1)*(reciprocalSum m c-1) = 2-c-(c⁻¹)^m := by
  have hci : c*c⁻¹=1 := mul_inv_cancel₀ hc.ne'
  have expand : reciprocalSum m c=(∑ j ∈ range m, (c⁻¹)^j)*c⁻¹ := by
    unfold reciprocalSum
    simp only [pow_succ,Finset.sum_mul]
  rw [expand]
  have h := geom_sum_mul c⁻¹ m
  linear_combination (∑ j ∈ range m, (c⁻¹)^j)*hci-h

theorem threshold_opens_right {n : ℕ} {c d : ℝ} (hc : 1<c) (hd : c<d)
    (root : (2-c)*c^(n+1)=1) : (2-d)*d^(n+1)<1 := by
  have hc0 : 0<c := by linarith
  have hd0 : 0<d := hc0.trans hd
  have hcroot : 2-c=(c⁻¹)^(n+1) := by
    rw [inv_pow,←one_div]
    exact (eq_div_iff (pow_ne_zero _ hc0.ne')).2 root
  have zero : (c-1)*(reciprocalSum (n+1) c-1)=0 := by
    rw [window_identity hc0,hcroot,sub_self]
  have rc : reciprocalSum (n+1) c=1 := sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left (by linarith))
  have ltinv : d⁻¹<c⁻¹ := inv_lt_inv₀ hd0 hc0 |>.2 hd
  have dec : reciprocalSum (n+1) d<reciprocalSum (n+1) c := by
    apply sum_lt_sum
    · intro j _
      exact pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) ltinv.le _
    · exact ⟨0,mem_range.mpr (Nat.zero_lt_succ n),by simpa using ltinv⟩
  have neg : (d-1)*(reciprocalSum (n+1) d-1)<0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith only [rc,dec])
  rw [window_identity hd0] at neg
  apply (lt_div_iff₀ (pow_pos hd0 (n+1))).1
  rw [one_div,←inv_pow]
  linarith only [neg]

#print axioms threshold_opens_right
end FullRankWindow
