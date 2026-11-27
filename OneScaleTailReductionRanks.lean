import OneScaleTailReduction

open Finset Set
open scoped BigOperators

namespace OneScale

/-- Increasing list of both canonical ladders, before cutting it off at c. -/
noncomputable def rung (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => ladderValue c 1
  | 2 => ladderValue c 2
  | 3 => ladderValue c 3
  | 4 => branchValue c 0
  | n+5 => (1+rung c (n+3))/c

/-- With the bottom atom as the first summand, the first winning target rank. -/
def advance (i : ℕ) : ℕ := if i<3 then i+1 else i+2

theorem rung_ordinary (c : ℝ) (j : ℕ) : rung c (2*j+3) = ladderValue c (j+3) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2*(j+1)+3=(2*j)+5 by omega]
    change (1+rung c (2*j+3))/c = (1+ladderValue c (j+3))/c
    rw [ih]

theorem rung_branching (c : ℝ) (j : ℕ) : rung c (2*j+4) = branchValue c j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2*(j+1)+4=(2*j+1)+5 by omega]
    change (1+rung c (2*j+4))/c = (1+branchValue c j)/c
    rw [ih]

theorem rung_strictMono {c : ℝ} (hc : 1<c) (hg : c<golden) : StrictMono (rung c) := by
  have h := ladderValue_strictMono hc hg
  apply strictMono_nat_of_lt_succ
  intro i
  by_cases hl : i<3
  · interval_cases i
    · exact h (show 0<1 by decide)
    · exact h (show 1<2 by decide)
    · exact h (show 2<3 by decide)
  · let j := (i-3)/2
    have hp : i=2*j+3 ∨ i=2*j+4 := by dsimp [j]; omega
    rcases hp with he|he
    · rw [he,rung_ordinary,show 2*j+3+1=2*j+4 by omega,rung_branching]
      exact (canonical_interlace hc hg j).1
    · rw [he,rung_branching,show 2*j+4+1=2*(j+1)+3 by omega,rung_ordinary]
      exact (canonical_interlace hc hg j).2

theorem canonical_iff_rung (c t : ℝ) : CanonicalLevel c t ↔ ∃ i, t=rung c i := by
  constructor
  · rintro (⟨n,rfl⟩|⟨j,rfl⟩)
    · by_cases h : n<3
      · interval_cases n
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨2,rfl⟩
      · exact ⟨_,by simpa [show n-3+3=n by omega] using (rung_ordinary c (n-3)).symm⟩
    · exact ⟨_,(rung_branching c j).symm⟩
  · rintro ⟨i,rfl⟩
    by_cases h : i<3
    · interval_cases i
      · exact Or.inl ⟨0,rfl⟩
      · exact Or.inl ⟨1,rfl⟩
      · exact Or.inl ⟨2,rfl⟩
    · let j := (i-3)/2
      have hp : i=2*j+3 ∨ i=2*j+4 := by dsimp [j]; omega
      rcases hp with h|h
      · exact Or.inl ⟨_,h ▸ rung_ordinary c j⟩
      · exact Or.inr ⟨_,h ▸ rung_branching c j⟩

theorem rung_advance (c : ℝ) (i : ℕ) : rung c (advance i)=(1+rung c i)/c := by
  by_cases h : i<3
  · interval_cases i <;> rfl
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ i by omega)
    rw [advance,if_neg h,show 3+j+2=j+5 by omega,show 3+j=j+3 by omega]
    rfl

/-- A coefficient-free winning predicate on integer ranks. -/
def RankWin (i j k : ℕ) : Prop :=
  (i=0 ∧ advance j≤k) ∨ (j=0 ∧ advance i≤k) ∨ (i=1 ∧ j=1 ∧ 4≤k)

theorem rank_edge_iff {c : ℝ} (hc : 1<c) (hg : c<golden) (i j k : ℕ) (hk : rung c k<c) :
    rung c i+rung c j≤c*rung c k ↔ RankWin i j k := by
  have hr := rung_strictMono hc hg
  have canon (s : ℕ) := (canonical_iff_rung c _).2 ⟨s,rfl⟩
  rw [canonical_edge_iff hc hg (canon i) (canon j) hk]
  change (_=rung c 0 ∧ _≤_) ∨ (_=rung c 0 ∧ _≤_) ∨
    (_=rung c 1 ∧ _=rung c 1 ∧ rung c 4≤_) ↔ _
  simp only [← rung_advance,hr.le_iff_le,hr.injective.eq_iff,RankWin]

/-- Cubic objective on the first N integer ranks, independent of the coefficient. -/
noncomputable def rankScore {N : ℕ} (w : Fin N → ℝ) : ℝ := by
  classical exact ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, if RankWin i j k then w i*w j*w k else 0

/-- Each chamber value is the maximum of a coefficient-free cubic on a simplex.
Its dimension is determined exactly by the number of active rungs. -/
theorem beta_integer_ranks {c : ℝ} (hc : 1<c) (hg : c<golden) :
    ∃ N : ℕ, (∀ i, i<N ↔ rung c i<c) ∧
      IsGreatest {b : ℝ | ∃ w : Fin N → ℝ, Mass w ∧ rankScore w=b} (beta c) := by
  classical
  obtain ⟨S,hs,w,hw,hβ,_⟩ := beta_fixed_canonical_menu hc hg
  have hm := rung_strictMono hc hg
  have inS (i : ℕ) : rung c i ∈ S ↔ rung c i<c := by
    rw [hs]
    exact and_iff_right ((canonical_iff_rung c _).mpr ⟨i,rfl⟩)
  have exit_ : ∃ n : ℕ, ¬rung c n<c := by
    by_contra! h
    let f : ℕ → S := fun i => ⟨_,(inS i).mpr (h i)⟩
    have hf : Function.Injective f := fun _ _ he => hm.injective (congrArg Subtype.val he)
    haveI : Finite ℕ := Finite.of_injective f hf
    exact not_finite ℕ
  let N := Nat.find exit_
  have hN (i : ℕ) : i<N ↔ rung c i<c := by
    constructor
    · exact fun hi => not_not.mp (Nat.find_min exit_ hi)
    · intro hi
      apply lt_of_not_ge
      intro hn
      exact Nat.find_spec exit_ ((hm.monotone hn).trans_lt hi)
  let z (i : Fin N) := rung c i
  have hz : Cfg c z := fun i => ⟨hm.monotone (Nat.zero_le i.val),(hN i).mp i.isLt⟩
  let e (i : Fin N) : S := ⟨z i,(inS i).mpr (hz i).2⟩
  have he : Function.Bijective e := by
    constructor
    · exact fun i j h => Fin.ext (hm.injective (congrArg Subtype.val h))
    · intro t
      obtain ⟨ht,htc⟩ := (hs t).mp t.property
      obtain ⟨i,hi⟩ := (canonical_iff_rung c _).mp ht
      refine ⟨⟨i,(hN i).mpr (hi ▸ htc)⟩,Subtype.ext hi.symm⟩
  let eqv : Fin N ≃ S := Equiv.ofBijective e he
  have image_eq (a : S) : z (eqv.symm a)=a.val := by
    exact congrArg Subtype.val (eqv.apply_symm_apply a)
  have hrank (v : Fin N → ℝ) : weakScore c z v=rankScore v := by
    simp only [weakScore,rankScore,WeakWin,z,rank_edge_iff hc hg _ _ _ ((hN _).mp (Fin.isLt _))]
  have hg' := (before_golden hc).mp hg
  have hc2 : c<2 := by nlinarith [sq_nonneg (c-1)]
  obtain ⟨x,hx,hwin⟩ := realize_weak_pattern hc2 z hz
  have hscore (v : Fin N → ℝ) : score c x v=rankScore v := by
    simp only [score,rankScore,hwin,WeakWin,z,rank_edge_iff hc hg _ _ _ ((hN _).mp (Fin.isLt _))]
  have lift := score_push eqv.symm c x w
  have hscores : score c (x ∘ eqv.symm) w=weakScore c Subtype.val w := by
    have hh (i j k : S) : Win c (x ∘ eqv.symm) i j k ↔ WeakWin c Subtype.val i j k := by
      simpa only [Win,Function.comp_apply,WeakWin,image_eq] using hwin (eqv.symm i) (eqv.symm j) (eqv.symm k)
    simp only [score,weakScore,hh]
  refine ⟨N,hN,⟨push eqv.symm w,mass_push eqv.symm hw,?_⟩,?_⟩
  · rw [← hscore,lift,hscores,hβ]
  · rintro b ⟨v,hv,rfl⟩
    rw [← hrank]
    exact le_csSup (bdd_values c) (weakScore_mem_values hc2 hz hv)

#print axioms beta_integer_ranks

end OneScale
