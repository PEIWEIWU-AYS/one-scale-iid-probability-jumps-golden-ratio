import EndpointAsymptotics.RankThresholdMonotone
import Height

noncomputable section
namespace MultinacciBands

private theorem exp_dominates (m : ℕ) (hm : 32≤m) : 4*(m:ℝ)≤(3/2:ℝ)^m := by
  induction m,hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [Nat.cast_succ,pow_succ]
    have h : (32:ℝ)≤m := by exact_mod_cast hm
    linarith

/-- A logarithmic shift that fits within the available number of bands. -/
theorem choose_delay (m : ℕ) (hm : 32≤m) :
    ∃ d : ℕ, 1≤d ∧ d≤m ∧ 4*(m:ℝ)≤(3/2:ℝ)^d ∧
      (d:ℝ)<Real.log (4*(m:ℝ))/Real.log (3/2)+1 := by
  let a := Real.log (4*(m:ℝ))/Real.log (3/2)
  have mlo : (32:ℝ)≤m := by exact_mod_cast hm
  have pos : 0<Real.log (3/2) := Real.log_pos (by norm_num)
  have h4 : 1<4*(m:ℝ) := by linarith
  have a0 : 0<a := div_pos (Real.log_pos h4) pos
  refine ⟨⌈a⌉₊,Nat.ceil_pos.mpr a0,Nat.ceil_le.mpr ?_,?_,Nat.ceil_lt_add_one a0.le⟩
  · have l := Real.log_le_log (zero_lt_one.trans h4) (exp_dominates m hm)
    rw [Real.log_pow] at l
    exact (div_le_iff₀ pos).mpr l
  · apply (Real.log_le_log_iff (zero_lt_one.trans h4) (by positivity)).mp
    rw [Real.log_pow]
    exact (div_le_iff₀ pos).mp (Nat.le_ceil a)

/-- The band ratio 2−1/m satisfies both geometric conditions at c_m. -/
theorem parameters {m d : ℕ} {c : ℝ} (hm : 32≤m) (hc : 1<c) (hc2 : c<2)
    (root : (2-c)*c^m=1) (shift : 4*(m:ℝ)≤(3/2:ℝ)^d) :
    let r := 2-1/(m:ℝ)
    1<r ∧ r*(1+(r⁻¹)^d)≤c ∧ (r⁻¹)^(m+2)≤2-c := by
  classical
  let r := 2-1/(m:ℝ)
  let t := 2-1/(2*(m:ℝ))
  have mlo : (32:ℝ)≤m := by exact_mod_cast hm
  have mp : 0<(m:ℝ) := by linarith
  have mp' : 0<2*(m:ℝ) := by positivity
  have invm : 1/(m:ℝ)≤1/2 := (div_le_iff₀ mp).mpr (by linarith)
  have invm2 : 1/(2*(m:ℝ))≤1/2 := (div_le_iff₀ mp').mpr (by linarith)
  have rbig : 3/2≤r := by dsimp only [r];linarith
  have tbig : 3/2≤t := by dsimp only [t];linarith
  have r1 : 1<r := (by norm_num : (1:ℝ)<3/2).trans_le rbig
  have rp : 0<r := zero_lt_one.trans r1
  have r2 : r≤2 := by dsimp only [r];linarith only [one_div_pos.mpr mp]
  have tc : t≤c := by
    by_contra! ht
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
    change m=k+1 at hk
    have hroot : (2-c)*c^(k+1)=1 := by simpa only [←hk] using root
    have opened := FullRankWindow.threshold_opens_right hc ht hroot
    rw [←hk] at opened
    have p := (exp_dominates m hm).trans (pow_le_pow_left₀ (by norm_num) tbig m)
    have a : 2-t=1/(2*(m:ℝ)) := by dsimp only [t];ring
    rw [a,one_div_mul_eq_div] at opened
    have small := (div_lt_iff₀ mp').mp opened
    linarith only [p,small,mp]
  have pd := shift.trans (pow_le_pow_left₀ (by norm_num) rbig d)
  have id : (r⁻¹)^d ≤ 1/(4*(m:ℝ)) := by
    rw [inv_pow,←one_div]
    exact one_div_le_one_div_of_le (by positivity) pd
  have tiny := mul_le_mul_of_nonneg_left id rp.le
  have tiny' := mul_le_mul_of_nonneg_right r2 (show 0≤1/(4*(m:ℝ)) by positivity)
  have gate : r*(1+(r⁻¹)^d)≤c := by
    apply le_trans _ tc
    have rt : r+2*(1/(4*(m:ℝ)))=t := by dsimp only [r,t];field_simp;ring
    linarith only [tiny,tiny',rt]
  have bern := one_add_mul_sub_le_pow (show -1≤r/2 by linarith) m
  have left : 1+(m:ℝ)*(r/2-1)=1/2 := by dsimp only [r];field_simp;ring
  rw [left,div_pow] at bern
  have b := (le_div_iff₀ (show 0<(2:ℝ)^m by positivity)).mp bern
  have sq : 2≤r^2 := (by norm_num : (2:ℝ)≤(3/2)^2).trans (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2) rbig 2)
  have width : c^m≤r^(m+2) := by
    rw [pow_add]
    have mul := mul_le_mul_of_nonneg_left sq (pow_nonneg rp.le m)
    have cp := pow_le_pow_left₀ (zero_lt_one.trans hc).le hc2.le m
    linarith only [mul,b,cp]
  have eq : 2-c=1/c^m := (eq_div_iff (pow_pos (zero_lt_one.trans hc) m).ne').mpr root
  refine ⟨r1,gate,?_⟩
  rw [eq,inv_pow,←one_div]
  exact one_div_le_one_div_of_le (pow_pos (zero_lt_one.trans hc) m) width

#print axioms choose_delay
#print axioms parameters
end MultinacciBands
