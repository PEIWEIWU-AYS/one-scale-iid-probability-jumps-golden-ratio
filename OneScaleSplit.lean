import OneScaleModel

open Finset
open scoped BigOperators

namespace OneScale

private lemma wider_window {c T : ℝ} (hc : 1 < c) (hφ : c*c < c+1)
    (hT : 1 ≤ T) (hTc : T < c) :
    ∃ d U : ℝ, c < d ∧ d*d < d+1 ∧ T < U ∧ U < d ∧ 1+T < d*U := by
  let p : ℝ := (1 + Real.sqrt 5) / 2
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsp : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hpp : 1 < p := by dsimp [p]; nlinarith
  have hp : 0 < p := by linarith
  have he : p*p = p+1 := by dsimp [p]; nlinarith
  have hcp : c < p := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ c+p-1 by linarith)]
  have hTp : T < p := lt_trans hTc hcp
  have hdivp : (1+T)/p < p := (div_lt_iff₀ hp).mpr (by linarith)
  obtain ⟨U,hU,hUp⟩ := exists_between (max_lt hTp hdivp)
  have hTU : T < U := lt_of_le_of_lt (le_max_left ..) hU
  have hUp0 : 0 < U := by linarith
  have hU1 : (1+T)/p < U := lt_of_le_of_lt (le_max_right ..) hU
  have hu1 : 1+T < U*p := (div_lt_iff₀ hp).mp hU1
  have hdivu : (1+T)/U < p := (div_lt_iff₀ hUp0).mpr (by linarith)
  obtain ⟨d,hd,hdp⟩ := exists_between (max_lt (max_lt hcp hUp) hdivu)
  have hd1 : max c U < d := lt_of_le_of_lt (le_max_left ..) hd
  have hcd : c < d := lt_of_le_of_lt (le_max_left ..) hd1
  have hud : U < d := lt_of_le_of_lt (le_max_right ..) hd1
  have hdu : (1+T)/U < d := lt_of_le_of_lt (le_max_right ..) hd
  exact ⟨d,U,hcd,by nlinarith [mul_pos (sub_pos.mpr hdp) (show 0 < p+d-1 by linarith)],
    hTU,hud,(div_lt_iff₀ hUp0).mp hdu⟩

private noncomputable def raised {α : Type*} [DecidableEq α] (x : α → ℝ)
    (h : α) (U : ℝ) (i : α × Bool) : ℝ :=
  if i.1 = h ∧ i.2 = true then U else x i.1

private lemma duplicate_sum {α : Type*} [Fintype α] (f : α → ℝ) :
    ∑ q : α × Bool, f q.1 = 2 * ∑ i, f i := by
  rw [Fintype.sum_prod_type]
  simp [Fintype.sum_bool, two_mul, Finset.sum_add_distrib]

private lemma duplicate_score {α : Type*} [Fintype α] (c : ℝ) (x w : α → ℝ) :
    score c (fun q : α × Bool => x q.1) (fun q => w q.1 / 2) = score c x w := by
  classical
  let t (i j k : α) : ℝ := if Win c x i j k then w i*w j*w k else 0
  have ht (i j k : α × Bool) :
      (if Win c (fun q : α × Bool => x q.1) i j k then
        (w i.1/2)*(w j.1/2)*(w k.1/2) else 0) = t i.1 j.1 k.1 / 8 := by
    dsimp [t,Win]
    split_ifs <;> ring
  unfold score
  simp_rw [ht]
  simp_rw [← Finset.sum_div]
  have triple (f : α → α → α → ℝ) :
      (∑ i : α × Bool, ∑ j : α × Bool, ∑ k : α × Bool, f i.1 j.1 k.1) =
      8 * ∑ i, ∑ j, ∑ k, f i j k := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
    ring
  rw [triple]
  dsimp [t]
  ring

/-- Splitting the largest atom preserves all old wins and introduces at least one new win. -/
theorem split_improvement {α : Type*} [Fintype α] {c : ℝ} {x w : α → ℝ}
    (hc : 1 < c) (hφ : c*c < c+1) (hx : Cfg c x) (hw : Mass w)
    (hpos : ∀ i, 0 < w i) (hmin : ∃ i, x i = 1) :
    ∃ (d : ℝ) (y v : α × Bool → ℝ), c < d ∧ d*d < d+1 ∧
      Cfg d y ∧ Mass v ∧ score c x w < score d y v := by
  classical
  obtain ⟨b,hb⟩ := hmin
  obtain ⟨h,_,hh⟩ := Finset.exists_max_image (Finset.univ : Finset α) x
    ⟨b,Finset.mem_univ _⟩
  have hmax (i : α) : x i ≤ x h := hh i (Finset.mem_univ _)
  obtain ⟨d,U,hcd,hdphi,hU,hUd,hnew⟩ :=
    wider_window hc hφ (hx h).1 (hx h).2
  let y := raised x h U
  let v : α × Bool → ℝ := fun q => w q.1 / 2
  have hy (i : α × Bool) : x i.1 ≤ y i := by
    dsimp [y,raised]
    split_ifs with hh'
    · exact le_trans (hmax _) hU.le
    · rfl
  have htop : c * x h < 1+x h := by
    nlinarith [mul_lt_mul_of_pos_left (hx h).2 (sub_pos.mpr hc)]
  have hxk (k : α) : c*x k ≤ c*x h := mul_le_mul_of_nonneg_left (hmax k) (by linarith)
  have hxpos (k : α) : 0 < x k := by linarith [(hx k).1]
  have preserve (i j k : α × Bool) (hwin : Win c (fun q : α × Bool => x q.1) i j k) :
      Win d y i j k := by
    change x i.1+x j.1 < c*x k.1 at hwin
    have hi : i.1 ≠ h := by rintro he; rw [he] at hwin; linarith [(hx j.1).1, hxk k.1]
    have hj : j.1 ≠ h := by rintro he; rw [he] at hwin; linarith [(hx i.1).1, hxk k.1]
    have hg : x i.1+x j.1 < d*y k :=
      lt_of_lt_of_le (lt_trans hwin (mul_lt_mul_of_pos_right hcd (hxpos _)))
        (mul_le_mul_of_nonneg_left (hy k) (by linarith))
    simpa [Win,y,raised,hi,hj] using hg
  have hold : ¬Win c (fun q : α × Bool => x q.1) (b,false) (h,false) (h,true) := by
    simp [Win,hb]; linarith
  have hgain : Win d y (b,false) (h,false) (h,true) := by
    simpa [Win,y,raised,hb] using hnew
  have hvp (i : α × Bool) : 0 < v i := by exact div_pos (hpos _) (by norm_num)
  have leterm (i j k : α × Bool) :
      (if Win c (fun q : α × Bool => x q.1) i j k then v i*v j*v k else 0) ≤
      (if Win d y i j k then v i*v j*v k else 0) := by
    by_cases hp : Win c (fun q : α × Bool => x q.1) i j k
    · simp [hp,preserve i j k hp]
    · simp only [if_neg hp]
      split_ifs
      · exact (mul_pos (mul_pos (hvp _) (hvp _)) (hvp _)).le
      · rfl
  refine ⟨d,y,v,hcd,hdphi,?_,?_,?_⟩
  · intro q
    constructor
    · exact le_trans (hx _).1 (hy _)
    · dsimp [y,raised]
      split_ifs
      · exact hUd
      · exact lt_trans (hx _).2 hcd
  · refine ⟨fun i => (hvp i).le,?_⟩
    change (∑ i : α × Bool, w i.1/2) = 1
    rw [← Finset.sum_div,duplicate_sum,hw.2]
    norm_num
  · rw [← duplicate_score c x w]
    change score c (fun q : α × Bool => x q.1) v < score d y v
    unfold score
    apply Finset.sum_lt_sum
    · exact fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => leterm i j k
    · refine ⟨(b,false),Finset.mem_univ _,?_⟩
      apply Finset.sum_lt_sum
      · exact fun j _ => Finset.sum_le_sum fun k _ => leterm _ j k
      · refine ⟨(h,false),Finset.mem_univ _,?_⟩
        apply Finset.sum_lt_sum
        · exact fun k _ => leterm _ _ k
        · refine ⟨(h,true),Finset.mem_univ _,?_⟩
          simp only [if_neg hold,if_pos hgain]
          exact mul_pos (mul_pos (hvp _) (hvp _)) (hvp _)

private lemma sum_pos_support {α : Type*} [Fintype α] {w : α → ℝ} (hw : Mass w)
    (f : α → ℝ) (hf : ∀ i, w i = 0 → f i = 0) :
    (∑ i : {i : α // 0 < w i}, f i.1) = ∑ i, f i := by
  classical
  have hz : (∑ i : {i : α // ¬0 < w i}, f i.1) = 0 :=
    Finset.sum_eq_zero fun i _ => hf i.1 (le_antisymm (not_lt.mp i.2) (hw.1 _))
  simpa [hz] using (Fintype.sum_subtype_add_sum_subtype (fun i => 0 < w i) f)

private lemma score_pos_support {α : Type*} [Fintype α] (c : ℝ) (x w : α → ℝ)
    (hw : Mass w) :
    score c (fun i : {i : α // 0 < w i} => x i.1) (fun i => w i.1) = score c x w := by
  classical
  let t (i j k : α) : ℝ := if Win c x i j k then w i*w j*w k else 0
  let P := {i : α // 0 < w i}
  change (∑ i : P, ∑ j : P, ∑ k : P, t i.1 j.1 k.1) = ∑ i, ∑ j, ∑ k, t i j k
  calc
    _ = ∑ i : P, ∑ j : P, ∑ k : α, t i.1 j.1 k := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      apply sum_pos_support hw
      intro k hk
      simp [t,hk]
    _ = ∑ i : P, ∑ j : α, ∑ k : α, t i.1 j k := by
      refine Finset.sum_congr rfl fun i _ => ?_
      apply sum_pos_support hw (fun j : α => ∑ k : α, t i.1 j k)
      intro j hj
      simp [t,hj]
    _ = _ := by
      apply sum_pos_support hw (fun i : α => ∑ j : α, ∑ k : α, t i j k)
      intro i hi
      simp [t,hi]

private lemma score_mem_values_of_cfg {α : Type*} [Fintype α] {c : ℝ} {x w : α → ℝ}
    (hx : Cfg c x) (hw : Mass w) : score c x w ∈ values c := by
  classical
  let e := (Fintype.equivFin α).symm
  refine ⟨_,fun i => x (e i),fun i => w (e i),fun i => hx (e i),
    ⟨fun i => hw.1 (e i),(e.sum_comp w).trans hw.2⟩,?_⟩
  let t (i j k : α) : ℝ := if Win c x i j k then w i*w j*w k else 0
  change (∑ i, ∑ j, ∑ k, t (e i) (e j) (e k)) = ∑ i, ∑ j, ∑ k, t i j k
  calc
    _ = ∑ i, ∑ j, ∑ k, t (e i) (e j) k :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e.sum_comp _
    _ = ∑ i, ∑ j, ∑ k, t (e i) j k :=
      Finset.sum_congr rfl fun i _ => e.sum_comp (fun j : α => ∑ k, t (e i) j k)
    _ = _ := e.sum_comp (fun i : α => ∑ j, ∑ k, t i j k)

/-- Every finite configuration can be strictly improved at a parameter still below
the golden ratio. Entries of zero mass are removed before normalizing the smallest atom. -/
theorem improve_value {c a : ℝ} (hc : 1 < c) (hφ : c*c < c+1) (ha : a ∈ values c) :
    ∃ d b : ℝ, c < d ∧ d*d < d+1 ∧ b ∈ values d ∧ a < b := by
  classical
  obtain ⟨n,x,w,hx,hw,rfl⟩ := ha
  let P := {i : Fin n // 0 < w i}
  obtain ⟨j,_,hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (show (∑ i, w i) ≠ 0 by rw [hw.2]; norm_num)
  let j' : P := ⟨j,lt_of_le_of_ne (hw.1 j) (Ne.symm hj)⟩
  obtain ⟨m,_,hm⟩ := Finset.exists_min_image (Finset.univ : Finset P) (fun i : P => x i.1)
    ⟨j', Finset.mem_univ _⟩
  let z (i : P) := x i.1 / x m.1
  let v (i : P) := w i.1
  have hm1 := (hx m.1).1
  have hmp : 0 < x m.1 := by linarith
  have hz : Cfg c z := by
    intro i
    constructor
    · exact (one_le_div hmp).mpr (hm i (Finset.mem_univ _))
    · have hmul : c ≤ c*x m.1 := by nlinarith [mul_nonneg (show 0 ≤ c by linarith) (sub_nonneg.mpr hm1)]
      exact (div_lt_iff₀ hmp).mpr (lt_of_lt_of_le (hx i.1).2 hmul)
  have hv : Mass v := ⟨fun i => i.2.le,(sum_pos_support hw w fun _ h => h).trans hw.2⟩
  have he : score c z v = score c x w := by
    rw [← score_pos_support c x w hw]
    unfold score
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    have hwin : Win c z i j k ↔ x i.1 + x j.1 < c*x k.1 := by
      dsimp [Win,z]
      rw [← add_div,← mul_div_assoc,div_lt_div_iff_of_pos_right hmp]
    simp only [hwin]
    rfl
  obtain ⟨d,y,u,hcd,hdφ,hy,hu,hgain⟩ :=
    split_improvement hc hφ hz hv (fun i : P => i.2) ⟨m,div_self hmp.ne'⟩
  exact ⟨d,score d y u,hcd,hdφ,score_mem_values_of_cfg hy hu,he ▸ hgain⟩

end OneScale
