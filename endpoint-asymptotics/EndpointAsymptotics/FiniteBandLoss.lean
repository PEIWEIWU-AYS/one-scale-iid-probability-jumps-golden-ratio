import EndpointAsymptotics.BandLossKernel

open Finset OneScale BandLossKernel
open scoped BigOperators
noncomputable section
namespace QuantitativeBands

attribute [local instance] Classical.propDecidable

def tailMass {n : ℕ} (x w : Fin n → ℝ) (p : ℝ) : ℝ :=
  ∑ i ∈ univ.filter (fun i => p≤x i), w i

private def cell (t : ℕ → ℝ) (j : ℕ) (u : ℝ) := t j≤u ∧ u<t (j+1)
private def marked (t : ℕ → ℝ) (d j : ℕ) (u v b : ℝ) :=
  cell t j u ∧ cell t j v ∧ t (j+d)≤b
private noncomputable def markedFlag (t : ℕ → ℝ) (d j : ℕ) (u v b : ℝ) : ℝ := by
  classical exact flag (marked t d j u v b)

private theorem cells_unique {t : ℕ → ℝ} (mono : Monotone t) {i j : ℕ} {u : ℝ}
    (a : cell t i u) (b : cell t j u) : i=j := by
  rcases lt_trichotomy i j with ij|ij|ij
  · exact False.elim (not_lt_of_ge (le_trans (mono ij) b.1) a.2)
  · exact ij
  · exact False.elim (not_lt_of_ge (le_trans (mono ij) a.1) b.2)

private theorem marked_min {t : ℕ → ℝ} (mono : Monotone t) {d j : ℕ} {u v b : ℝ}
    (h : marked t d j u v b) : cell t j (min u (min v b)) := by
  exact ⟨le_min h.1.1 (le_min h.2.1.1 ((mono (Nat.le_add_right j d)).trans h.2.2)),
    (min_le_left _ _).trans_lt h.1.2⟩

private theorem marked_losses {t : ℕ → ℝ} (mono : Monotone t) {d j : ℕ} (hd : 0<d)
    {c u v b : ℝ} (hc : 0<c) (geom : c*t (j+1)≤t j+t (j+d)) (h : marked t d j u v b) :
    markedFlag t d j u v b+markedFlag t d j v b u+markedFlag t d j b u v≤tripleLoss c u v b := by
  have order := mono (show j+1≤j+d by omega)
  have nb : ¬cell t j b := fun hb => (not_lt_of_ge (order.trans h.2.2)) hb.2
  have n1 : ¬marked t d j v b u := fun hb => nb hb.2.1
  have n2 : ¬marked t d j b u v := fun hb => nb hb.1
  have lost1 : ¬v+b<c*u := by
    have up := mul_lt_mul_of_pos_left h.1.2 hc
    linarith only [geom,up,h.2.2,h.2.1.1]
  have lost2 : ¬b+u<c*v := by
    have up := mul_lt_mul_of_pos_left h.2.1.2 hc
    linarith only [geom,up,h.2.2,h.1.1]
  classical
  simp only [markedFlag,flag,if_pos h,if_neg n1,if_neg n2,add_zero,tripleLoss,wins,if_neg lost1,if_neg lost2]
  split_ifs <;> norm_num

private theorem cyclic_loss (c u v b : ℝ) : tripleLoss c v b u=tripleLoss c u v b := by
  unfold tripleLoss;ring

private theorem pointwise (t : ℕ → ℝ) (mono : Monotone t) (N d : ℕ) (hd : 0<d)
    {c : ℝ} (hc : 0<c) (h2 : c≤2) (geom : ∀ j, c*t (j+1)≤t j+t (j+d))
    {u v b : ℝ} (hu : 0≤u) (hv : 0≤v) (hb : 0≤b) :
    (∑ j ∈ range N, (markedFlag t d j u v b+markedFlag t d j v b u+markedFlag t d j b u v))≤tripleLoss c u v b := by
  classical
  let root := min u (min v b)
  have notIn (j : ℕ) (miss : ¬cell t j root) :
      markedFlag t d j u v b+markedFlag t d j v b u+markedFlag t d j b u v=0 := by
    have h1 : ¬marked t d j u v b := fun h => miss (marked_min mono h)
    have h2 : ¬marked t d j v b u := fun h => miss (by simpa [root,min_comm,min_assoc,min_left_comm] using marked_min mono h)
    have h3 : ¬marked t d j b u v := fun h => miss (by simpa [root,min_comm,min_assoc,min_left_comm] using marked_min mono h)
    simp [markedFlag,flag,h1,h2,h3]
  by_cases h : ∃ j∈range N, cell t j root
  · obtain ⟨j,mem,hr⟩ := h
    rw [sum_eq_single_of_mem j mem (fun i _ ne => notIn i (fun hi => ne (cells_unique mono hi hr)))]
    by_cases a : marked t d j u v b
    · exact marked_losses mono hd hc (geom j) a
    by_cases b' : marked t d j v b u
    · have p := marked_losses mono hd hc (geom j) b'
      rw [cyclic_loss] at p
      linarith only [p]
    by_cases z : marked t d j b u v
    · have p := marked_losses mono hd hc (geom j) z
      rw [cyclic_loss c v b u,cyclic_loss] at p
      linarith only [p]
    simp [markedFlag,flag,a,b',z,tripleLoss_nonneg h2 hu hv hb]
  · rw [sum_eq_zero fun i hi => notIn i (fun hit => h ⟨i,hi,hit⟩)]
    exact tripleLoss_nonneg h2 hu hv hb

private theorem cell_sum {n : ℕ} (x w : Fin n → ℝ) (t : ℕ → ℝ) (mono : Monotone t) (j : ℕ) :
    (∑ i, w i*(if cell t j (x i) then 1 else 0)) = tailMass x w (t j)-tailMass x w (t (j+1)) := by
  classical
  simp only [tailMass,Finset.sum_filter,←sum_sub_distrib]
  apply sum_congr rfl; intro i _
  by_cases h : t j≤x i <;> by_cases k : t (j+1)≤x i <;>
    simp [cell,h,k,lt_iff_not_ge]; linarith only [mono (Nat.le_succ j),h,k]

private theorem marked_avg {n : ℕ} (x w : Fin n → ℝ) (t : ℕ → ℝ) (mono : Monotone t) (d j : ℕ) :
    avg3 w (fun a b k => markedFlag t d j (x a) (x b) (x k)) =
    (tailMass x w (t j)-tailMass x w (t (j+1)))^2*tailMass x w (t (j+d)) := by
  classical
  let b := fun i => if cell t j (x i) then (1:ℝ) else 0
  let h := fun i => if t (j+d)≤x i then (1:ℝ) else 0
  have eq (a e k : Fin n) : markedFlag t d j (x a) (x e) (x k)=b a*b e*h k := by
    by_cases h1 : cell t j (x a) <;> by_cases h2 : cell t j (x e) <;> by_cases h3 : t (j+d)≤x k <;>
      simp [markedFlag,flag,marked,b,h,h1,h2,h3]
  simp_rw [eq]
  rw [avg3_product]
  have bs : (∑ i,w i*b i)=tailMass x w (t j)-tailMass x w (t (j+1)) := cell_sum x w t mono j
  rw [bs,pow_two]
  have th : (∑ i,w i*h i)=tailMass x w (t (j+d)) := by
    simp only [tailMass,Finset.sum_filter,h];apply sum_congr rfl;intro i _;split_ifs <;> simp_all
  rw [th]

private theorem avg3_sum {n : ℕ} (w : Fin n → ℝ) (N : ℕ) (f : ℕ → Fin n → Fin n → Fin n → ℝ) :
    avg3 w (fun i j k => ∑ e ∈ range N, f e i j k)=∑ e ∈ range N, avg3 w (f e) := by
  induction N with
  | zero => simp [avg3]
  | succ N ih => simp only [sum_range_succ,avg3_add,ih]

theorem finite_band_loss {n : ℕ} (K d : ℕ) (hd : 0<d) {c : ℝ} (hc : 0<c) (h2 : c≤2)
    (x w : Fin n → ℝ) (hx : ∀ i, 0≤x i) (hw : Mass w) (t : ℕ → ℝ) (mono : Monotone t)
    (geom : ∀ j, c*t (j+1)≤t j+t (j+d)) :
    ∑ i ∈ range K, (tailMass x w (t i)-tailMass x w (t (i+1)))^2*tailMass x w (t (i+d)) ≤ 2/3-score c x w := by
  let f := fun j i l k => markedFlag t d j (x i) (x l) (x k)
  have bound := avg3_mono hw.1 (fun i l k => pointwise t mono K d hd hc h2 geom (hx i) (hx l) (hx k))
  rw [avg3_sum,avg3_loss,hw.2,one_pow] at bound
  have eq (j : ℕ) : avg3 w (fun i l k => f j i l k+f j l k i+f j k i l) =
      3*((tailMass x w (t j)-tailMass x w (t (j+1)))^2*tailMass x w (t (j+d))) := by
    rw [avg3_add,avg3_add,avg3_rotate,avg3_rotate w (fun a b e => f j b e a),avg3_rotate]
    dsimp only [f];rw [marked_avg x w t mono d j];ring
  change (∑ j ∈ range K, avg3 w (fun i l k => f j i l k+f j l k i+f j k i l)) ≤ _ at bound
  simp_rw [eq] at bound
  rw [←mul_sum] at bound
  linarith only [bound]

#print axioms finite_band_loss
end QuantitativeBands
