import EndpointAsymptotics.FullRankDominance

open Finset OneScale
open scoped BigOperators
noncomputable section
namespace FullRankWindow

/-- Exact decomposition after removing the smallest coordinate (the last label). -/
theorem rank_remove_last {m : ℕ} (w : Fin (m+1) → ℝ) :
    rankScore w = rankScore (fun i : Fin m => w i.castSucc) +
    (w (Fin.last m))^2*(∑ i : Fin m, w i.castSucc) +
    2*w (Fin.last m)*(∑ i : Fin m, w i.castSucc)^2 := by
  classical
  have never (i : Fin m) : ¬Fin.last m < i.castSucc := not_lt_of_ge i.castSucc_lt_last.le
  simp only [rankScore,Fin.sum_univ_castSucc,Fin.castSucc_lt_castSucc_iff,Fin.castSucc_lt_last,
    never,lt_irrefl,false_or,or_false,true_or,or_true,if_true,if_false,
    sum_add_distrib,sum_const_zero,add_zero,zero_add,←mul_sum,←sum_mul]
  ring

private theorem rank_scale {m : ℕ} (p : ℝ) (w : Fin m → ℝ) :
    rankScore (fun i => p*w i) = p^3*rankScore w := by
  unfold rankScore
  rw [mul_sum]
  apply sum_congr rfl; intro i _
  rw [mul_sum]
  apply sum_congr rfl; intro j _
  rw [mul_sum]
  apply sum_congr rfl; intro k _
  split_ifs <;> ring

private def addSmall {m : ℕ} (p : ℝ) (w : Fin m → ℝ) : Fin (m+1) → ℝ :=
  Fin.lastCases (1-p) (fun i => p*w i)

private theorem addSmall_mass {m : ℕ} {p : ℝ} (hp : 0≤p) (hp1 : p≤1)
    (w : Fin m → ℝ) (hw : Mass w) : Mass (addSmall p w) := by
  constructor
  · intro i
    induction i using Fin.lastCases with
    | last => simpa [addSmall] using sub_nonneg.mpr hp1
    | cast j => simpa [addSmall] using mul_nonneg hp (hw.1 j)
  · rw [Fin.sum_univ_castSucc]
    simp only [addSmall,Fin.lastCases_castSucc,Fin.lastCases_last,←mul_sum,hw.2,mul_one]
    ring

private theorem addSmall_score {m : ℕ} (p : ℝ) (w : Fin m → ℝ) (hw : Mass w) :
    rankScore (addSmall p w) = p-(1-rankScore w)*p^3 := by
  rw [rank_remove_last]
  simp only [addSmall,Fin.lastCases_castSucc,Fin.lastCases_last,←mul_sum,hw.2,mul_one,rank_scale]
  ring

/-- The exact largest rank score for a block of n+1 labels. -/
def peak : ℕ → ℝ
  | 0 => 0
  | n+1 => 2/(3*Real.sqrt (3*(1-peak n)))

theorem peak_lt {n : ℕ} : peak n < 2/3 := by
  induction n with
  | zero => norm_num [peak]
  | succ n ih =>
    rw [peak]
    have hs := Real.sq_sqrt (show 0≤3*(1-peak n) by linarith)
    have hs' : 1<Real.sqrt (3*(1-peak n)) := by
      nlinarith only [ih,hs,Real.sqrt_nonneg (3*(1-peak n))]
    apply (div_lt_iff₀ (by positivity)).2
    linarith

private theorem peak_step (n : ℕ) :
    IsGreatest ((fun p : ℝ => p-(1-peak n)*p^3) '' Set.Icc 0 1) (peak (n+1)) := by
  let A := 1-peak n
  let s := Real.sqrt (3*A)
  have hA : 1/3<A := by dsimp [A]; linarith only [peak_lt (n:=n)]
  have hA0 : 0<A := (by norm_num : (0:ℝ)<1/3).trans hA
  have hs : s^2=3*A := Real.sq_sqrt (mul_nonneg (by norm_num) hA0.le)
  have hbig : 1<3*A := by
    have hh := (div_lt_iff₀ (by norm_num : (0:ℝ)<3)).1 hA
    simpa only [mul_comm A 3] using hh
  have hs0 : 0≤s := Real.sqrt_nonneg _
  have hs1 : 1<s := by
    by_contra! small
    have contra := pow_le_pow_left₀ hs0 small 2
    rw [hs,one_pow] at contra
    exact (not_le_of_gt hbig) contra
  have hsp : 0<s := by linarith
  let y := 1/s
  have hy : 0<y := one_div_pos.mpr hsp
  have hy1 : y≤1 := (div_le_one hsp).mpr hs1.le
  have crit : 3*A*y^2=1 := by
    rw [←hs]; dsimp [y]; field_simp
  have best : y-A*y^3=peak (n+1) := by
    change y-A*y^3=2/(3*s)
    have eq : 2/(3*s)=(2/3)*y := by dsimp [y];ring
    rw [eq]
    linear_combination -(y/3)*crit
  refine ⟨⟨y,⟨hy.le,hy1⟩,best⟩,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  change p-A*p^3≤peak (n+1)
  rw [←best]
  have id : (y-A*y^3)-(p-A*p^3)=A*(p-y)^2*(p+2*y) := by
    nlinarith only [congrArg (fun z : ℝ => z*(p-y)) crit]
  exact sub_nonneg.mp (id ▸ mul_nonneg (mul_nonneg hA0.le (sq_nonneg _))
    (add_nonneg hp.1 (mul_nonneg (by norm_num) hy.le)))

/-- Optimization is over all weight vectors, including boundary points. -/
theorem rank_peak (n : ℕ) :
    (∃ w : Fin (n+1) → ℝ, Mass w ∧ rankScore w=peak n) ∧
      (∀ w : Fin (n+1) → ℝ, Mass w → rankScore w≤peak n) := by
  induction n with
  | zero =>
    constructor
    · refine ⟨fun _ => 1,⟨fun _ => zero_le_one,by simp⟩,?_⟩
      simp [rankScore,peak]
    · intro w _
      simp [rankScore,peak]
  | succ n ih =>
    obtain ⟨⟨w,hw,hwin⟩,upper⟩ := ih
    obtain ⟨⟨p,hp,hval⟩,bound⟩ := peak_step n
    constructor
    · refine ⟨addSmall p w,addSmall_mass hp.1 hp.2 w hw,?_⟩
      rw [addSmall_score p w hw,hwin]
      exact hval
    · intro v hv
      let b := ∑ i : Fin (n+1), v i.castSucc
      have hb : 0≤b := sum_nonneg fun i _ => hv.1 _
      have total : b+v (Fin.last (n+1))=1 := by simpa only [b,Fin.sum_univ_castSucc] using hv.2
      have hb1 : b≤1 := by linarith [hv.1 (Fin.last (n+1))]
      by_cases zero : b=0
      · have each (i : Fin (n+1)) : v i.castSucc=0 := by
          have hle : v i.castSucc ≤ b := single_le_sum (fun j _ => hv.1 j.castSucc) (mem_univ i)
          exact le_antisymm (zero ▸ hle) (hv.1 _)
        rw [rank_remove_last]
        change rankScore (fun i : Fin (n+1) => v i.castSucc)+v (Fin.last (n+1))^2*b+
          2*v (Fin.last (n+1))*b^2 ≤ _
        simp only [zero,each,rankScore,zero_mul,ite_self,sum_const_zero,zero_pow (by decide : 2≠0),mul_zero,add_zero]
        exact (bound (a := 0) ⟨0,⟨le_rfl,zero_le_one⟩,by ring⟩)
      · let u (i : Fin (n+1)) := v i.castSucc/b
        have hu : Mass u := ⟨fun i => div_nonneg (hv.1 _) hb,by
          dsimp only [u];rw [←sum_div];exact div_self zero⟩
        have he : (fun i : Fin (n+1) => v i.castSucc) = fun i => b*u i := by
          funext i; dsimp only [u]; field_simp
        have bu : rankScore (fun i : Fin (n+1) => v i.castSucc) ≤ b^3*peak n := by
          rw [he,rank_scale]
          exact mul_le_mul_of_nonneg_left (upper u hu) (pow_nonneg hb 3)
        rw [rank_remove_last]
        have bnd := bound (a := b-(1-peak n)*b^3) ⟨b,⟨hb,hb1⟩,rfl⟩
        have last : v (Fin.last (n+1))=1-b := by linarith
        change rankScore (fun i : Fin (n+1) => v i.castSucc)+v (Fin.last (n+1))^2*b+2*v (Fin.last (n+1))*b^2 ≤ _
        rw [last]
        nlinarith only [bu,bnd]

#print axioms rank_remove_last
#print axioms rank_peak
end FullRankWindow
