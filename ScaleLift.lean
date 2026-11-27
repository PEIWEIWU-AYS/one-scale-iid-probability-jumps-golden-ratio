import OneScaleGolden

open Set Filter IidJumpSpectra MeasureTheory
open scoped BigOperators Topology
noncomputable section
namespace OneScale

private def term {α : Type*} (c : ℝ) (x w : α → ℝ) (i j k : α) : ℝ := by
  classical exact if Win c x i j k then w i * w j * w k else 0

private def blockTerm {α γ : Type*} (c p t : ℝ) (y v : α → ℝ) (x w : γ → ℝ) :
    (α ⊕ γ) → (α ⊕ γ) → (α ⊕ γ) → ℝ
  | .inl i, .inl j, .inl k => p^3 * term c y v i j k
  | .inl i, .inl j, .inr k => p^2*t * (v i * (v j * w k))
  | .inl i, .inr j, .inr k => p*t^2 * (v i * (w j * w k))
  | .inr i, .inl j, .inr k => p*t^2 * (w i * (v j * w k))
  | .inr i, .inr j, .inr k => t^3 * term c x w i j k
  | _, _, _ => 0

private theorem block_sum {α γ : Type*} [Fintype α] [Fintype γ] (c p t : ℝ)
    (y v : α → ℝ) (x w : γ → ℝ) (hv : Mass v) (hw : Mass w) :
    ∑ i, ∑ j, ∑ k, blockTerm c p t y v x w i j k =
    p^3 * score c y v + t^3 * score c x w + 2*p*t^2 + p^2*t := by
  classical
  simp only [Fintype.sum_sum_type, blockTerm, Finset.sum_add_distrib, Finset.sum_const_zero,
    add_zero, zero_add, ← Finset.mul_sum, hv.2, hw.2, mul_one]
  simp only [score, term]
  ring

private theorem combine_finite {n m : ℕ} [NeZero n] [NeZero m] {c p t : ℝ}
    (hc : 1 < c) (hp : 0 ≤ p) (ht : 0 ≤ t) (hpt : p+t=1)
    (y v : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) (hv : Mass v)
    (x w : Fin m → ℝ) (hx : Cfg c x) (hw : Mass w) :
    p^3 * score c y v + t^3 * score c x w + 2*p*t^2 + p^2*t ≤ extremal 2 c := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  obtain ⟨b,_,hb⟩ := Finset.exists_max_image Finset.univ y Finset.univ_nonempty
  let e := min (c/4) ((c-x a)/2)
  have he : 0 < e := lt_min (by linarith) (by linarith [(hx a).2])
  let s := e / (y b + 1)
  have hs : 0 < s := div_pos he (by linarith [hy b])
  have hsy (i) : s*y i < e := by
    have hd : 0 < y b+1 := by linarith [hy b]
    rw [show s*y i = (e*y i)/(y b+1) by dsimp [s]; ring,div_lt_iff₀ hd]
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr (hb i (Finset.mem_univ _)))]
  let z := Sum.elim (fun i => s*y i) x
  let q := Sum.elim (fun i => p*v i) (fun j => t*w j)
  have hz : ∀ i, 0 ≤ z i := by rintro (i|i); exact mul_nonneg hs.le (hy _); exact zero_le_one.trans (hx _).1
  have hq : Mass q := by
    refine ⟨?_,?_⟩
    · rintro (i|i); exact mul_nonneg hp (hv.1 i); exact mul_nonneg ht (hw.1 i)
    · simp [q,Fintype.sum_sum_type,← Finset.mul_sum,hv.2,hw.2,hpt]
  obtain ⟨μ,hμ,_,hm⟩ := weighted_law c z q hz hq
  haveI := hμ
  have htarget (k) : c ≤ c*x k := by nlinarith [mul_nonneg (show 0 ≤ c by linarith) (sub_nonneg.mpr (hx k).1)]
  have hlo (i j : Fin n) (k : Fin m) : s*y i + s*y j < c*x k := by
    linarith [hsy i,hsy j,show e ≤ c/4 from min_le_left ..,htarget k]
  have hmixed (i : Fin n) (j k : Fin m) : s*y i + x j < c*x k := by
    linarith [hsy i,show e ≤ (c-x a)/2 from min_le_right ..,
      ha j (Finset.mem_univ _), (hx a).2,htarget k]
  have hscale (i j k : Fin n) : (s*y i+s*y j < c*(s*y k)) ↔ y i+y j < c*y k := by
    rw [← mul_add,show c*(s*y k)=s*(c*y k) by ring]
    exact mul_lt_mul_left hs
  have point (i j k) : blockTerm c p t y v x w i j k ≤ term c z q i j k := by
    have nonnegT (a b d) : 0 ≤ term c z q a b d := by
      unfold term; split_ifs; exact mul_nonneg (mul_nonneg (hq.1 _) (hq.1 _)) (hq.1 _); rfl
    cases i <;> cases j <;> cases k <;> simp only [blockTerm]
    all_goals first | exact nonnegT _ _ _ | skip
    all_goals simp only [term,Win,z,q,Sum.elim_inl,Sum.elim_inr]
    all_goals first | rw [if_pos (hlo ..)] | rw [if_pos (hmixed ..)] |
      rw [add_comm (x _) (s*_), if_pos (hmixed ..)] | skip
    all_goals try simp only [hscale]
    all_goals try split_ifs
    all_goals apply le_of_eq; ring
  rw [← block_sum c p t y v x w hv hw]
  apply le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    Finset.sum_le_sum fun k _ => point i j k)
  change score c z q ≤ _
  rw [← hm]
  exact iidWin_le_extremal _ _ _

private theorem low_above {c b : ℝ} (hb : b < extremal 2 c) :
    ∃ (n : ℕ) (_ : NeZero n) (y v : Fin n → ℝ), (∀ i, 0 ≤ y i) ∧
      Mass v ∧ b < score c y v := by
  have he := (survival_tendsto 3).eventually_const_lt
    (show b + 1 - extremal 2 c < 1 by linarith)
  obtain ⟨n,hn,hs⟩ := ((eventually_ge_atTop 1).and he).exists
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨y,hy,hw⟩ := exists_sample_above (m := 2) (N := n) (c := c) (b := b) (by linarith)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  refine ⟨n,inferInstance,y,fun _ => 1/(n:ℝ),hy,⟨fun _ => by positivity,?_⟩,?_⟩
  · simp [hn']
  · rwa [uniform_score]

/-- The separated-scale lower bound with an arbitrary upper-block mass.
Both suprema range over their original Borel probability laws. -/
theorem scale_lift {c t : ℝ} (hc : 1 < c) (ht : 0 < t) (ht1 : t < 1) :
    (1-t)^3 * extremal 2 c + t^3 * beta c + 2*(1-t)*t^2 + (1-t)^2*t ≤ extremal 2 c := by
  let p := 1-t
  have hp : 0 < p := sub_pos.mpr ht1
  have hp3 : 0 < p^3 := pow_pos hp _
  have ht3 : 0 < t^3 := pow_pos ht _
  let R := 2*p*t^2 + p^2*t
  suffices h : beta c ≤ (extremal 2 c - p^3 * extremal 2 c - R)/t^3 by
    have h' := (le_div_iff₀ ht3).mp h
    dsimp [p,R] at h'
    linarith
  apply csSup_le (values_nonempty hc)
  rintro b ⟨m,x,w,hx,hw,rfl⟩
  have hm : m ≠ 0 := by
    rintro rfl
    simpa using hw.2
  letI : NeZero m := ⟨hm⟩
  apply (le_div_iff₀ ht3).2
  by_contra! bad
  have hb : (extremal 2 c - t^3*score c x w - R)/p^3 < extremal 2 c :=
    (div_lt_iff₀ hp3).2 (by linarith)
  obtain ⟨n,hn,y,v,hy,hv,hg⟩ := low_above hb
  letI := hn
  have a := combine_finite hc hp.le ht.le (show p+t=1 by dsimp [p]; ring)
    y v hy hv x w hx hw
  have g := (div_lt_iff₀ hp3).mp hg
  dsimp [R] at g
  linarith

/-- Explicit unconditional lower bound for the unrestricted optimum at φ. -/
theorem unrestricted_golden_lower : (Real.sqrt 61 - 5)/6 ≤ extremal 2 golden := by
  let a := Real.sqrt 61
  have ha : a^2 = 61 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha7 : 7 < a := by nlinarith
  have ha8 : a < 8 := by nlinarith
  let t := (13-a)/9
  have ht : 0 < t := by dsimp [t]; linarith
  have ht' : t < 1 := by dsimp [t]; linarith
  have h := scale_lift one_lt_golden ht ht'
  rw [beta_golden] at h
  let D := 1-(1-t)^3
  have hD : 0 < D := by
    dsimp [D]
    exact sub_pos.mpr (pow_lt_one₀ (sub_nonneg.mpr ht'.le) (by linarith) (by decide))
  have hel : D*((a-5)/6) = t^3*(1/4) + 2*(1-t)*t^2 + (1-t)^2*t := by
    dsimp [D,t]
    have h3 : a^3=61*a := by rw [pow_succ,ha]
    have h4 : a^4=61^2 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,ha]
    ring_nf
    simp only [h4,h3,ha]
    ring
  change (a-5)/6 ≤ _
  apply (le_of_mul_le_mul_left _ hD)
  rw [hel]
  dsimp [D]
  linarith

#print axioms scale_lift
#print axioms unrestricted_golden_lower
end OneScale
