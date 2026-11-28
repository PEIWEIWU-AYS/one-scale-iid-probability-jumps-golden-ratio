import ScaleLift

open Set Filter IidJumpSpectra MeasureTheory OneScale
open scoped BigOperators Topology
noncomputable section
namespace ClosedSpectrum

/-- The total weight of weakly winning triples in a finite block. -/
def closedScore {α : Type*} [Fintype α] (c : ℝ) (x w : α → ℝ) : ℝ := by
  classical exact ∑ i, ∑ j, ∑ k, if x i+x j ≤ c*x k then w i*w j*w k else 0

/-- The total weight of weakly winning ordered pairs in a finite block. -/
def closedPairs {α : Type*} [Fintype α] (c : ℝ) (x w : α → ℝ) : ℝ := by
  classical exact ∑ i, ∑ k, if x i ≤ c*x k then w i*w k else 0

/-- The fixed point for repeated copies of the same block, with top mass t. -/
def blockValue (t B Q : ℝ) : ℝ :=
  (t^3*B+2*(1-t)*t^2*Q+(1-t)^2*t)/(1-(1-t)^3)

theorem blockValue_odds (B Q : ℝ) {r : ℝ} (hr : 0≤r) :
    blockValue (1/(1+r)) B Q = (B+2*r*Q+r^2)/(1+3*r+3*r^2) := by
  have h1 : 0 < 1+r := by linarith
  have h2 : 0 < 1+3*r+3*r^2 := by positivity
  have den : 1-(1-1/(1+r))^3=(1+3*r+3*r^2)/(1+r)^3 := by
    field_simp; ring
  unfold blockValue
  rw [den,div_div_eq_mul_div]
  field_simp
  ring

private def term {α : Type*} (c : ℝ) (x w : α → ℝ) (i j k : α) : ℝ := by
  classical exact if Win c x i j k then w i*w j*w k else 0

private def pair {γ : Type*} (c : ℝ) (x w : γ → ℝ) (j k : γ) : ℝ := by
  classical exact if x j ≤ c*x k then w j*w k else 0

private def triple {γ : Type*} (c : ℝ) (x w : γ → ℝ) (i j k : γ) : ℝ := by
  classical exact if x i+x j ≤ c*x k then w i*w j*w k else 0

private def mixedTerm {α γ : Type*} (d c p t : ℝ) (y v : α → ℝ) (x w : γ → ℝ) :
    (α ⊕ γ) → (α ⊕ γ) → (α ⊕ γ) → ℝ
  | .inl i, .inl j, .inl k => p^3 * term d y v i j k
  | .inl i, .inl j, .inr k => p^2*t * (v i*(v j*w k))
  | .inl i, .inr j, .inr k => p*t^2 * (v i*pair c x w j k)
  | .inr i, .inl j, .inr k => p*t^2 * (v j*pair c x w i k)
  | .inr i, .inr j, .inr k => t^3 * triple c x w i j k
  | _, _, _ => 0

private theorem mixed_sum {α γ : Type*} [Fintype α] [Fintype γ] (d c p t : ℝ)
    (y v : α → ℝ) (x w : γ → ℝ) (hv : Mass v) (hw : Mass w) :
    ∑ i, ∑ j, ∑ k, mixedTerm d c p t y v x w i j k =
      p^3*score d y v + t^3*closedScore c x w + 2*p*t^2*closedPairs c x w + p^2*t := by
  classical
  simp only [Fintype.sum_sum_type,mixedTerm,Finset.sum_add_distrib,Finset.sum_const_zero,
    add_zero,zero_add,← Finset.mul_sum,← Finset.sum_mul,hv.2,hw.2,mul_one,one_mul]
  simp only [closedScore,closedPairs,score,pair,triple,term]
  ring

private theorem combine {n m : ℕ} [NeZero n] [NeZero m] {c d p t : ℝ}
    (hc : 0<c) (hcd : c<d) (hp : 0≤p) (ht : 0≤t) (hpt : p+t=1)
    (y v : Fin n → ℝ) (hy : ∀ i, 0≤y i) (hv : Mass v)
    (x w : Fin m → ℝ) (hx : ∀ i, 0<x i) (hw : Mass w) :
    p^3*score d y v + t^3*closedScore c x w + 2*p*t^2*closedPairs c x w + p^2*t
      ≤ extremal 2 d := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  obtain ⟨b,_,hb⟩ := Finset.exists_max_image Finset.univ y Finset.univ_nonempty
  let e := min ((d*x a)/4) ((d-c)*x a)
  have hd : 0<d := hc.trans hcd
  have he : 0<e := lt_min (div_pos (mul_pos hd (hx a)) (by norm_num)) (mul_pos (sub_pos.mpr hcd) (hx a))
  let s := e / (y b+1)
  have hs : 0<s := div_pos he (by linarith [hy b])
  have hsy (i) : s*y i<e := by
    rw [show s*y i=(e*y i)/(y b+1) by dsimp [s]; ring,
      div_lt_iff₀ (show 0<y b+1 by linarith [hy b])]
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr (hb i (Finset.mem_univ _)))]
  let z := Sum.elim (fun i => s*y i) x
  let q := Sum.elim (fun i => p*v i) (fun j => t*w j)
  have hz : ∀ i, 0≤z i := by rintro (i|i); exact mul_nonneg hs.le (hy _); exact (hx _).le
  have hq : Mass q := by
    refine ⟨?_,?_⟩
    · rintro (i|i); exact mul_nonneg hp (hv.1 i); exact mul_nonneg ht (hw.1 i)
    · simp [q,Fintype.sum_sum_type,← Finset.mul_sum,hv.2,hw.2,hpt]
  obtain ⟨μ,hμ,_,heq⟩ := weighted_law d z q hz hq
  haveI := hμ
  have hlo (i j : Fin n) (k : Fin m) : s*y i+s*y j<d*x k := by
    have hmin := mul_le_mul_of_nonneg_left (ha k (Finset.mem_univ _)) hd.le
    linarith [hsy i,hsy j,show e ≤ d*x a/4 from min_le_left ..,mul_pos hd (hx a)]
  have hmixed (i : Fin n) (j k : Fin m) (h : x j≤c*x k) : s*y i+x j<d*x k := by
    have hmin := mul_le_mul_of_nonneg_left (ha k (Finset.mem_univ _)) (sub_nonneg.mpr hcd.le)
    nlinarith only [hsy i,show e ≤ (d-c)*x a from min_le_right ..,hmin,h]
  have hhigh (i j k : Fin m) (h : x i+x j≤c*x k) : x i+x j<d*x k :=
    h.trans_lt (mul_lt_mul_of_pos_right hcd (hx _))
  have hscale (i j k : Fin n) : (s*y i+s*y j<d*(s*y k)) ↔ y i+y j<d*y k := by
    rw [← mul_add,show d*(s*y k)=s*(d*y k) by ring]
    exact mul_lt_mul_left hs
  have point (i j k) : mixedTerm d c p t y v x w i j k ≤ term d z q i j k := by
    have pos (a b k) : 0≤term d z q a b k := by
      unfold term; split_ifs; exact mul_nonneg (mul_nonneg (hq.1 _) (hq.1 _)) (hq.1 _); rfl
    cases i <;> cases j <;> cases k <;> simp only [mixedTerm]
    all_goals first | exact pos _ _ _ | skip
    all_goals simp only [term,Win,z,q,Sum.elim_inl,Sum.elim_inr,pair,triple]
    all_goals try rw [if_pos (hlo ..)]
    all_goals try simp only [hscale]
    all_goals try rw [add_comm (x _) (s*_)]
    all_goals try split_ifs
    all_goals first
      | (exfalso; apply_assumption; apply hmixed; assumption)
      | (exfalso; apply_assumption; apply hhigh; assumption)
      | (apply le_of_eq; ring; done)
      | (simp only [mul_zero]; repeat' first | apply mul_nonneg | exact hp | exact ht | exact hv.1 _ | exact hw.1 _)
  rw [← mixed_sum d c p t y v x w hv hw]
  apply le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    Finset.sum_le_sum fun k _ => point i j k)
  change score d z q ≤ _
  rw [← heq]
  exact iidWin_le_extremal _ _ _

private theorem near_extremal {d b : ℝ} (hb : b<extremal 2 d) :
    ∃ (n : ℕ) (_ : NeZero n) (y v : Fin n → ℝ), (∀ i, 0≤y i) ∧ Mass v ∧ b<score d y v := by
  have he := (survival_tendsto 3).eventually_const_lt (show b+1-extremal 2 d<1 by linarith)
  obtain ⟨n,hn,hs⟩ := ((eventually_ge_atTop 1).and he).exists
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨y,hy,hw⟩ := exists_sample_above (m:=2) (N:=n) (c:=d) (b:=b) (by linarith)
  have hn' : (n:ℝ)≠0 := by exact_mod_cast (NeZero.ne n)
  refine ⟨n,inferInstance,y,fun _ => 1/(n:ℝ),hy,⟨fun _ => by positivity,?_⟩,?_⟩
  · simp [hn']
  · rwa [uniform_score]

theorem closedBlock_le_right {c d t : ℝ} (hc : 0<c) (hcd : c<d) (ht : 0<t) (ht1 : t≤1)
    {n : ℕ} (x w : Fin n → ℝ) (hx : ∀ i, 0<x i) (hw : Mass w) :
    blockValue t (closedScore c x w) (closedPairs c x w) ≤ extremal 2 d := by
  let p := 1-t
  have hp : 0≤p := sub_nonneg.mpr ht1
  have hp1 : p<1 := by dsimp [p]; linarith
  have hn : n≠0 := by rintro rfl; simpa using hw.2
  letI : NeZero n := ⟨hn⟩
  have hS : p^3*extremal 2 d + t^3*closedScore c x w + 2*p*t^2*closedPairs c x w + p^2*t
      ≤ extremal 2 d := by
    by_cases h0 : p=0
    · obtain ⟨N,hN,y,v,hy,hv,_⟩ := near_extremal (d:=d) (b:=extremal 2 d-1) (by linarith)
      letI := hN
      simpa [h0] using combine hc hcd hp ht.le (show p+t=1 by dsimp [p]; ring) y v hy hv x w hx hw
    · have hp3 : 0<p^3 := pow_pos (lt_of_le_of_ne hp (Ne.symm h0)) _
      by_contra! bad
      have hsmall :
          (extremal 2 d-t^3*closedScore c x w-2*p*t^2*closedPairs c x w-p^2*t)/p^3 < extremal 2 d :=
        (div_lt_iff₀ hp3).2 (by linarith)
      obtain ⟨N,hN,y,v,hy,hv,above⟩ := near_extremal hsmall
      letI := hN
      have bound := combine hc hcd hp ht.le (show p+t=1 by dsimp [p]; ring) y v hy hv x w hx hw
      have big := (div_lt_iff₀ hp3).1 above
      linarith
  apply (div_le_iff₀ (sub_pos.mpr (pow_lt_one₀ hp hp1 (by decide : 3≠0)))).2
  dsimp [p] at hS ⊢
  linarith

#print axioms blockValue_odds
#print axioms closedBlock_le_right
end ClosedSpectrum
