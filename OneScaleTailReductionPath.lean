import OneScaleTailReductionRanks
import OneScaleTailGraph

open Finset
open scoped BigOperators

namespace OneScale

/-- Masses at the bottom, first and second ordinary rungs followed by the tail. -/
def rankMass {n : ℕ} (p u t : ℝ) (w : Fin n → ℝ) : Fin (n+3) → ℝ :=
  Fin.cons p (Fin.cons u (Fin.cons t w))

private theorem rank_expand {n : ℕ} (p u t : ℝ) (w : Fin n → ℝ) :
    rankScore (rankMass p u t w) =
      p^2*(u+t+∑ i,w i) + 2*p*u*(t+∑ i,w i) + 2*p*t*(∑ i,w i) +
        (∑ i : Fin n, ((if i.val=0 then 0 else u^2)*w i +
          ∑ j : Fin n, (if i.val+1 < j.val ∨ j.val+1 < i.val then p else 0)*w i*w j)) := by
  classical
  have splitF (i j : Fin n) :
      (if i.val+1 < j.val ∨ j.val+1 < i.val then p*w i*w j else 0) =
        (if i.val+1 < j.val then p*w i*w j else 0) +
        (if j.val+1 < i.val then p*w j*w i else 0) := by
    split_ifs <;> first | omega | ring
  have symm : (∑ i : Fin n, ∑ j : Fin n, if j.val+1 < i.val then p*w j*w i else 0) =
      (∑ i : Fin n, ∑ j : Fin n, if i.val+1 < j.val then p*w i*w j else 0) := by
    rw [Finset.sum_comm]
  have neg (i : ℕ) : ¬ i+1+1+1<3 := by omega
  have nex0 (i : ℕ) : i+1+1+1+2 ≠ 0 := by omega
  have nex1 (i : ℕ) : ¬ i+1+1+1+2 ≤ 1 := by omega
  have nex2 (i : ℕ) : ¬ i+1+1+1+2 ≤ 2 := by omega
  have crel (i j : ℕ) : i+1+1+1+2≤j+1+1+1 ↔ i+1<j := by omega
  have bonus (i : Fin n) : (if 1 ≤ i.val then u*u*w i else 0) =
      (if i.val=0 then 0 else u^2*w i) := by split_ifs <;> first | omega | ring
  simp [rankScore,rankMass,Fin.sum_univ_succ,RankWin,advance,Fin.val_succ,neg,nex0,nex1,nex2,crel]
  simp only [bonus,splitF,Finset.sum_add_distrib,symm,mul_comm (w _) p,← Finset.mul_sum]
  ring

/-- Equality between the ordered rank optimization and the path polynomial. -/
theorem rankScore_pathRaw {n : ℕ} (p u t : ℝ) (w : Fin n → ℝ)
    (hw : Tail.PathValid p u t w) : rankScore (rankMass p u t w) = Tail.pathRaw p u t w := by
  rw [rank_expand]
  have ht : u+t+(∑ i,w i)=1-p := by linarith [hw.2.2.2.2]
  rw [ht]
  rfl

private theorem mass_rankMass {n : ℕ} (p u t : ℝ) (w : Fin n → ℝ) :
    Mass (rankMass p u t w) ↔ Tail.PathValid p u t w := by
  simp only [Mass,Tail.PathValid,rankMass,Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ,
    Fin.sum_univ_succ]
  constructor <;> rintro ⟨a,b⟩
  · exact ⟨a.1,a.2.1,a.2.2.1,a.2.2.2,by linarith⟩
  · exact ⟨⟨a,b.1,b.2.1,b.2.2.1⟩,by linarith [b.2.2.2]⟩

/-- The two programs have exactly the same attainable values, for every tail length. -/
theorem rank_path_values (n : ℕ) :
    {b : ℝ | ∃ a : Fin (n+3) → ℝ, Mass a ∧ rankScore a=b} =
    {b : ℝ | ∃ (p u t : ℝ) (w : Fin n → ℝ), Tail.PathValid p u t w ∧ Tail.pathRaw p u t w=b} := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    let p := a 0
    let u := a (Fin.succ 0)
    let t := a (Fin.succ (Fin.succ 0))
    let w (i : Fin n) := a i.succ.succ.succ
    have he : rankMass p u t w=a := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      refine Fin.cases ?_ (fun d => ?_) k
      · rfl
      · rfl
    have hv := (mass_rankMass p u t w).mp (he ▸ ha)
    exact ⟨p,u,t,w,hv,(rankScore_pathRaw p u t w hv).symm.trans (congrArg rankScore he)⟩
  · rintro ⟨p,u,t,w,hv,rfl⟩
    exact ⟨_,(mass_rankMass p u t w).mpr hv,rankScore_pathRaw p u t w hv⟩

/-- Exact path reduction of the original optimum for every c with precisely n+3 ranks. -/
theorem beta_path_raw {c : ℝ} (hc : 1<c) (hg : c<golden) {n : ℕ}
    (ha : ∀ i, i<n+3 ↔ rung c i<c) :
    IsGreatest {b : ℝ | ∃ (p u t : ℝ) (w : Fin n → ℝ),
      Tail.PathValid p u t w ∧ Tail.pathRaw p u t w=b} (beta c) := by
  obtain ⟨N,hN,hβ⟩ := beta_integer_ranks hc hg
  have he : N = n+3 := by
    have H (i : ℕ) := (hN i).trans (ha i).symm
    have h1 := (H N).not
    have h2 := (H (n+3)).not
    omega
  subst N
  rwa [← rank_path_values]

#print axioms beta_path_raw

end OneScale
