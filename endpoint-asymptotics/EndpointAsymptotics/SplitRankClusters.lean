import EndpointAsymptotics.FullRankTransfer
import EndpointAsymptotics.RankModelSequence
open Finset OneScale ClosedSpectrum IidJumpSpectra
open scoped BigOperators
noncomputable section
namespace FullRankWindow

private def site (a : ℝ) (x : ℝ) (b : Bool) : ℝ := if b then x else a*x

private theorem site_bounds {a x : ℝ} (ha : a≤1) (hx : 0≤x) (b : Bool) :
    a*x ≤ site a x b ∧ site a x b ≤ x := by
  have l := mul_le_mul_of_nonneg_right ha hx
  cases b <;> simp [site,show a*x≤x by simpa using l]

private def paid {n : ℕ} (i j k : Fin n) (a b t : Bool) : Prop :=
  k < i ∨ k < j ∨ (i=k ∧ j=k ∧ t=true ∧ (a=false ∨ b=false))
private instance {n : ℕ} (i j k : Fin n) (a b t : Bool) : Decidable (paid i j k a b t) := by
  unfold paid; infer_instance

private theorem split_rank_score {n : ℕ} {c d a : ℝ} (hc : 0<c) (ha : 0<a) (ha1 : a≤1)
    (slack : d<c*a) (micro : 1+a<c) (x w : Fin n → ℝ)
    (hx : ∀ i,0<x i) (hw : Mass w)
    (wins : ∀ i j k, k < i ∨ k < j → x i + x j ≤ d*x k) :
    rankScore w + 3/8*(∑ i, (w i)^3) ≤ extremal 2 c := by
  classical
  let y (u : Fin n × Bool) := site a (x u.1) u.2
  let v (u : Fin n × Bool) := w u.1 / 2
  have hwin (i j k : Fin n) (e f g : Bool) (h : paid i j k e f g) :
      Win c y (i,e) (j,f) (k,g) := by
    change site a (x i) e + site a (x j) f < c*site a (x k) g
    have large (h : k < i ∨ k < j) : _ := calc
      site a (x i) e + site a (x j) f ≤ x i + x j :=
        add_le_add (site_bounds ha1 (hx i).le e).2 (site_bounds ha1 (hx j).le f).2
      _ ≤ d*x k := wins _ _ _ h
      _ < (c*a)*x k := mul_lt_mul_of_pos_right slack (hx k)
      _ ≤ c*site a (x k) g := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (site_bounds ha1 (hx k).le g).1 hc.le
    rcases h with hi|hj|⟨rfl,rfl,rfl,he⟩
    · exact large (Or.inl hi)
    · exact large (Or.inr hj)
    · have hm := mul_lt_mul_of_pos_right micro (hx j)
      have hl := mul_le_mul_of_nonneg_right ha1 (hx j).le
      rcases he with rfl|rfl
      · cases f <;> simp only [site,ite_false,ite_true,Bool.false_eq_true,ite_true,ite_false,reduceCtorEq] <;> linarith
      · cases e <;> simp only [site,ite_false,ite_true,Bool.false_eq_true,ite_true,ite_false,reduceCtorEq] <;> linarith
  let term (i j k : Fin n) (e f g : Bool) : ℝ :=
    if paid i j k e f g then (w i/2)*(w j/2)*(w k/2) else 0
  have bits (i j k : Fin n) : ∑ e, ∑ f, ∑ g, term i j k e f g =
      (if k < i ∨ k < j then w i*w j*w k else 0) +
      (if i=k ∧ j=k then (3/8)*(w k)^3 else 0) := by
    by_cases h : k < i ∨ k < j
    · have ne : ¬ (i=k ∧ j=k) := by rintro ⟨rfl,rfl⟩; simp at h
      simp [term,paid,←or_assoc,h,ne,Fintype.sum_bool]
      ring
    · simp only [term,paid,←or_assoc,h,false_or,if_false,Fintype.sum_bool,zero_add]
      by_cases e : i=k ∧ j=k
      · rcases e with ⟨rfl,rfl⟩; simp; ring
      · push_neg at e
        by_cases u : i=k <;> by_cases v' : j=k <;> simp_all
  have hv : Mass v := by
    refine ⟨fun i => div_nonneg (hw.1 _) (by norm_num),?_⟩
    rw [Fintype.sum_prod_type]; simp only [v,Fintype.sum_bool,add_halves]; exact hw.2
  have hy (u : Fin n × Bool) : 0≤y u := (mul_nonneg ha.le (hx _).le).trans (site_bounds ha1 (hx _).le _).1
  obtain ⟨μ,hμ,_,hval⟩ := weighted_law c y v hy hv
  haveI := hμ
  let paidTerm (u z t : Fin n × Bool) := term u.1 z.1 t.1 u.2 z.2 t.2
  have term_le (u z t : Fin n × Bool) : paidTerm u z t ≤
      if Win c y u z t then v u*v z*v t else 0 := by
    dsimp only [paidTerm,term,v]
    split_ifs with h h' h'
    · exact le_rfl
    · exact False.elim (h' (hwin _ _ _ _ _ _ h))
    · exact mul_nonneg (mul_nonneg (hv.1 u) (hv.1 z)) (hv.1 t)
    · exact le_rfl
  have reorder : (∑ u, ∑ z, ∑ t, paidTerm u z t) =
      ∑ i, ∑ j, ∑ k, ∑ e, ∑ f, ∑ g, term i j k e f g := by
    simp only [Fintype.sum_prod_type,paidTerm]
    apply sum_congr rfl; intro i _
    rw [sum_comm]
    apply sum_congr rfl; intro j _
    simp_rw [Finset.sum_comm (s := (univ : Finset Bool)) (t := (univ : Finset (Fin n)))]
  have lower : rankScore w + 3/8*(∑ i, (w i)^3) ≤ score c y v := by
    have h := sum_le_sum (s:=univ) (fun u _ => sum_le_sum (s:=univ) (fun z _ =>
      sum_le_sum (s:=univ) (fun t _ => term_le u z t)))
    rw [reorder] at h
    simp_rw [bits] at h
    convert h using 1
    simp [rankScore,sum_add_distrib,Finset.mul_sum,ite_and]
  exact lower.trans (hval ▸ iidWin_le_extremal 2 c μ)

/-- Splitting every coarse rank into two preserves all its wins and, already at
the exact threshold for n+5 labels, earns a fixed fraction of its diagonal mass. -/
theorem split_rank_lower {n : ℕ} {c : ℝ} (hc : 15/8<c) (hc2 : c<2)
    (root : (2-c)*c^(n+5)=1) (w : Fin (n+1) → ℝ) (hw : Mass w) :
    rankScore w + 3/8*(∑ i, (w i)^3) ≤ extremal 2 c := by
  let d := 2-8*(2-c)
  let a := 1-2*(2-c)
  have hd : 1<d := by dsimp [d]; linarith
  have hd2 : d<2 := by dsimp [d]; linarith
  have hdc : d≤c := by dsimp [d]; linarith
  have hpow : (8:ℝ)≤c^4 := by
    have z := pow_le_pow_left₀ (by norm_num) hc.le 4
    norm_num at z; linarith
  have h0 : 0≤2-c := by linarith
  have hwin : (2-d)*d^(n+1)≤1 := calc
    _ = 8*(2-c)*d^(n+1) := by dsimp [d]; ring
    _ ≤ 8*(2-c)*c^(n+1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hdc _) (by positivity)
    _ ≤ c^4*((2-c)*c^(n+1)) := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hpow (mul_nonneg h0 (pow_nonneg (by linarith) (n+1)))
    _ = 1 := by rw [←root,show n+5=n+1+4 by omega,pow_add]; ring
  obtain ⟨x,_,pos,_,he⟩ := (weak_iff hd hd2).2 hwin
  apply split_rank_score (by linarith : 0<c) (a:=a) (d:=d)
    (by dsimp [a];linarith) (by dsimp [a];linarith) ?_ (by dsimp [a];linarith)
    (fun i => x i.val) w (fun i => pos _ (by omega)) hw
    (fun i j k h => (he _ (by omega) _ (by omega) _ (by omega)).2 h)
  dsimp [d,a]
  nlinarith only [hc2,sq_nonneg (2-c)]
#print axioms split_rank_lower
end FullRankWindow
