import EndpointAsymptotics.RankPopulationEndpoint

open Finset
open scoped BigOperators
noncomputable section
namespace QuantitativeBands

private theorem shifted_sum_le (K j d : ℕ) (hj : j≤d) (f : ℕ → ℝ) (hf : ∀ i, 0≤f i) :
    ∑ i ∈ range K, f (i+j) ≤ ∑ i ∈ range (K+d), f i := by
  have h := sum_range_add f j K
  have h₁ : ∑ i ∈ range K, f (i+j) ≤ ∑ i ∈ range (j+K), f i := by
    rw [h]
    simpa only [Nat.add_comm j] using le_add_of_nonneg_left (a:=∑ i ∈ range K, f (j+i))
      (sum_nonneg (fun i _ => hf i) : 0≤∑ i ∈ range j, f i)
  exact h₁.trans (sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun i _ _ => hf i))

private theorem telescope (T : ℕ → ℝ) (i k : ℕ) :
    ∑ j ∈ range k, (T (i+j)-T (i+j+1))=T i-T (i+k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ,ih]; simp only [Nat.add_succ]; ring

private theorem shifted_mass (a : ℕ → ℝ) (K d : ℕ) :
    ∑ i ∈ range K, ∑ j ∈ range d, a i*a (i+j) ≤
      (d:ℝ)*∑ i ∈ range (K+d), (a i)^2 := by
  rw [sum_comm]
  have each (j : ℕ) (hj : j∈range d) : ∑ i ∈ range K, a i*a (i+j) ≤
      ∑ i ∈ range (K+d), (a i)^2 := by
    have s := shifted_sum_le K j d (mem_range.mp hj).le (fun i => (a i)^2) (fun _ => sq_nonneg _)
    have s₀ := shifted_sum_le K 0 d (Nat.zero_le _) (fun i => (a i)^2) (fun _ => sq_nonneg _)
    simp only [Nat.add_zero] at s₀
    have am := sum_le_sum (s:=range K) (fun i _ =>
      show 2*(a i*a (i+j))≤(a i)^2+(a (i+j))^2 by nlinarith only [sq_nonneg (a i-a (i+j))])
    rw [sum_add_distrib,←mul_sum] at am
    linarith only [s,s₀,am]
  simpa only [sum_const,card_range,nsmul_eq_mul] using sum_le_sum each

/-- The sum lost by replacing each square root of a tail mass by its value
`d` bands later, controlled by the observed disjoint-band loss. -/
theorem delayed_root_loss (K d : ℕ) (T : ℕ → ℝ) {ε H : ℝ} (he : 0<ε)
    (mono : Antitone T) (tail : ∀ i, ε≤T i)
    (loss : ∑ i ∈ range (K+d), (T i-T (i+1))^2*T (i+d) ≤ H) :
    2*Real.sqrt ε*ε*(∑ i ∈ range K, (T i-T (i+1))*(Real.sqrt (T i)-Real.sqrt (T (i+d))))
      ≤(d:ℝ)*H := by
  let a := fun i => T i-T (i+1)
  have pos (i : ℕ) : 0≤T i := he.le.trans (tail i)
  have sqbound : ε*(∑ i ∈ range (K+d), (a i)^2)≤H := by
    rw [mul_sum]
    exact (sum_le_sum (fun i _ => (mul_comm ε ((a i)^2)).le.trans
      (mul_le_mul_of_nonneg_left (tail (i+d)) (sq_nonneg _)))).trans loss
  have localbd (i : ℕ) : 2*Real.sqrt ε*(a i*(Real.sqrt (T i)-Real.sqrt (T (i+d)))) ≤
      ∑ j ∈ range d, a i*a (i+j) := by
    have hdiff := Real.sqrt_le_sqrt (mono (Nat.le_add_right i d))
    have lows := Real.sqrt_le_sqrt (tail (i+d))
    have factor := mul_nonneg (sub_nonneg.mpr hdiff)
      (show 0≤Real.sqrt (T i)+Real.sqrt (T (i+d))-2*Real.sqrt ε by linarith only [hdiff,lows])
    rw [←mul_sum,show (∑ j ∈ range d, a (i+j))=T i-T (i+d) from telescope T i d]
    have single : 2*Real.sqrt ε*(Real.sqrt (T i)-Real.sqrt (T (i+d))) ≤ T i-T (i+d) := by
      nlinarith only [factor,Real.sq_sqrt (pos i),Real.sq_sqrt (pos (i+d))]
    nlinarith only [mul_le_mul_of_nonneg_left single (show 0≤a i from sub_nonneg.mpr (mono (Nat.le_succ i)))]
  have allbd := sum_le_sum (s:=range K) (fun i _ => localbd i)
  rw [←mul_sum] at allbd
  have comparison := allbd.trans (shifted_mass a K d)
  have scaled := mul_le_mul_of_nonneg_left comparison he.le
  have cap := mul_le_mul_of_nonneg_left sqbound (Nat.cast_nonneg d)
  change 2*Real.sqrt ε*ε*(∑ i ∈ range K, a i*(Real.sqrt (T i)-Real.sqrt (T (i+d)))) ≤ _
  linarith only [scaled,cap]

private theorem stieltjes_lower (K : ℕ) (T : ℕ → ℝ) (pos : ∀ i, 0≤T i) :
    (2/3:ℝ)*((Real.sqrt (T 0))^3-(Real.sqrt (T K))^3) ≤
      ∑ i ∈ range K, (T i-T (i+1))*Real.sqrt (T i) := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have h := mul_nonneg (sq_nonneg (Real.sqrt (T k)-Real.sqrt (T (k+1))))
      (show 0≤Real.sqrt (T k)+2*Real.sqrt (T (k+1)) by positivity)
    have one : (2/3:ℝ)*((Real.sqrt (T k))^3-(Real.sqrt (T (k+1)))^3) ≤
        (T k-T (k+1))*Real.sqrt (T k) := by
      nth_rw 2 [←Real.sq_sqrt (pos k)]
      nth_rw 2 [←Real.sq_sqrt (pos (k+1))]
      nlinarith only [h]
    linarith only [ih,one]

/-- Finite-band concentration bound leading to the explicit unrestricted
estimate. The two hypotheses about probabilities are the disjoint middle-target
loss and the terminal-interval loss. -/
theorem effective_band_bound (K d : ℕ) (T : ℕ → ℝ) {ε q H : ℝ} (he : 0<ε)
    (hH : 0≤H) (mono : Antitone T) (tail : ∀ i, ε≤T i)
    (h0 : T 0=1) (hK : T K=ε+q) (chooseE : ε^3=(d:ℝ)*H)
    (terminal : q^3≤6*(d:ℝ)*H)
    (loss : ∑ i ∈ range (K+d), (T i-T (i+1))^2*T (i+d) ≤ H) :
    (2/3:ℝ) ≤ (Real.sqrt K+4*Real.sqrt d)*Real.sqrt H := by
  let a := fun i => T i-T (i+1)
  have pos (i : ℕ) : 0≤T i := he.le.trans (tail i)
  have tpos : 0≤(d:ℝ) := Nat.cast_nonneg _
  have epos := Real.sqrt_pos.2 he
  have ee := Real.sq_sqrt he.le
  have rootD := Real.sq_sqrt tpos
  have rootH := Real.sq_sqrt hH
  have mult : Real.sqrt ε*ε=Real.sqrt d*Real.sqrt H := by
    have eq : (Real.sqrt ε*ε)^2=(Real.sqrt d*Real.sqrt H)^2 := by
      rw [mul_pow,mul_pow,ee,rootD,rootH]; linear_combination chooseE
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp eq
  have sc : (∑ i ∈ range K, a i*Real.sqrt (T (i+d))) ≤ Real.sqrt K*Real.sqrt H := by
    have cs := sum_mul_sq_le_sq_mul_sq (range K) (fun _ => (1:ℝ)) (fun i => a i*Real.sqrt (T (i+d)))
    simp only [one_mul,one_pow,sum_const,card_range,nsmul_eq_mul,mul_one,mul_pow,
      Real.sq_sqrt (pos _)] at cs
    have en : ∑ i ∈ range K, (a i)^2*T (i+d)≤H :=
      (sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_add_right K d))
        (fun i _ _ => mul_nonneg (sq_nonneg _) (pos (i+d)))).trans loss
    apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),rootH]
    exact cs.trans (mul_le_mul_of_nonneg_left en (Nat.cast_nonneg _))
  have del := delayed_root_loss K d T he mono tail loss
  change 2*Real.sqrt ε*ε*(∑ i ∈ range K, a i*(Real.sqrt (T i)-Real.sqrt (T (i+d))))≤_ at del
  have dh : (d:ℝ)*H=(Real.sqrt ε*ε)^2 := by rw [mul_pow,ee]; linear_combination -chooseE
  rw [dh] at del
  have gain : (∑ i ∈ range K, a i*(Real.sqrt (T i)-Real.sqrt (T (i+d)))) ≤ Real.sqrt ε*ε/2 := by
    apply le_of_mul_le_mul_left (a:=Real.sqrt ε*ε) ?_ (mul_pos epos he)
    nlinarith only [del]
  have rm := stieltjes_lower K T pos
  rw [h0,Real.sqrt_one,one_pow,hK] at rm
  have rel : ∑ i ∈ range K, (T i-T (i+1))*Real.sqrt (T i) =
      (∑ i ∈ range K, a i*Real.sqrt (T (i+d))) +
      ∑ i ∈ range K, a i*(Real.sqrt (T i)-Real.sqrt (T (i+d))) := by
    rw [←sum_add_distrib];apply sum_congr rfl;intro i _;dsimp [a];ring
  rw [rel] at rm
  have small : q≤2*ε := by
    by_contra hn
    have lower : 2*ε<q := lt_of_not_ge hn
    have gt := pow_lt_pow_left₀ lower (by positivity : 0≤2*ε) (by decide : 3≠0)
    nlinarith only [gt,terminal,chooseE,pow_pos he 3]
  have sumroot := Real.sqrt_le_sqrt (show ε+q≤3*ε by linarith only [small])
  have three : Real.sqrt 3≤7/4 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤3)] at sumroot
  have cube := pow_le_pow_left₀ (Real.sqrt_nonneg _) sumroot 3
  have eq3 : (Real.sqrt 3)^3≤21/4 := by
    rw [pow_succ,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]; linarith only [three]
  rw [mul_pow] at cube
  have ec : (Real.sqrt ε)^3=Real.sqrt ε*ε := by rw [pow_succ,ee,mul_comm]
  rw [ec] at cube
  have cap := cube.trans (mul_le_mul_of_nonneg_right eq3 (by positivity))
  rw [mult] at cap gain
  nlinarith only [rm,sc,gain,cap]

#print axioms delayed_root_loss
#print axioms effective_band_bound
end QuantitativeBands
