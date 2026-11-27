import OneScaleJumps
import Mathlib.Tactic

open Finset Set Filter
open scoped BigOperators Topology
noncomputable section

namespace OneScale

private def dyadicLevel (j : ℕ) : ℝ := golden - (golden-1)*(1/2 : ℝ)^j

private lemma golden_square' : golden*golden = golden+1 := by
  dsimp [golden]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]

private lemma golden_lt_two' : golden < 2 := by
  by_contra! hh
  nlinarith [golden_square', mul_nonneg (sub_nonneg.mpr hh)
    (show 0 ≤ golden+1 by linarith [one_lt_golden])]

private lemma dyadic_bounds (j : ℕ) : 1 ≤ dyadicLevel j ∧ dyadicLevel j < golden := by
  have hp := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (n := j)
  have hp' : 0 < (1/2:ℝ)^j := by positivity
  have h := sub_pos.mpr one_lt_golden
  dsimp [dyadicLevel]
  constructor
  · nlinarith [mul_nonneg h.le (sub_nonneg.mpr hp)]
  · nlinarith [mul_pos h hp']

private lemma dyadic_mono : Monotone dyadicLevel := by
  intro i j hij
  dsimp [dyadicLevel]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij) (sub_nonneg.mpr one_lt_golden.le)) _

private lemma dyadic_strict (i : ℕ) :
    1 + dyadicLevel i < golden * dyadicLevel (i+1) := by
  have he := golden_square'
  have hpos := mul_pos (mul_pos (sub_pos.mpr one_lt_golden)
    (show 0 < (1/2:ℝ)^i by positivity)) (show 0 < 1 - golden/2 by linarith [golden_lt_two'])
  dsimp [dyadicLevel]
  rw [pow_succ]
  nlinarith

private lemma finite_dyadic {a : ℝ} (ha : a < golden) (n : ℕ) :
    ∃ c, max a 1 < c ∧ c < golden ∧
      Cfg c (fun i : Fin (n+1) => dyadicLevel i.val) ∧
      ∀ i j : Fin (n+1), i < j → 1 + dyadicLevel i.val < c * dyadicLevel j.val := by
  have ez : ∀ᶠ c in 𝓝 golden, ∀ i : Fin (n+1), dyadicLevel i.val < c :=
    Filter.eventually_all.mpr fun i => lt_mem_nhds (dyadic_bounds i.val).2
  have ep (i j : Fin (n+1)) : ∀ᶠ c in 𝓝 golden,
      i < j → 1 + dyadicLevel i.val < c * dyadicLevel j.val := by
    by_cases hij : i < j
    · have hg : 1 + dyadicLevel i.val < golden * dyadicLevel j.val :=
        (dyadic_strict i.val).trans_le (mul_le_mul_of_nonneg_left
          (dyadic_mono (show i.val+1 ≤ j.val from hij)) (by linarith [one_lt_golden]))
      have hct : ContinuousAt (fun c : ℝ => c * dyadicLevel j.val) golden := by fun_prop
      exact (hct.tendsto.eventually_const_lt hg).mono fun c h _ => h
    · exact Eventually.of_forall fun _ h => False.elim (hij h)
  have epall := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (ep i))
  have eleft : ∀ᶠ c in 𝓝[<] golden, c < golden := self_mem_nhdsWithin
  have eabove : ∀ᶠ c in 𝓝 golden, max a 1 < c := lt_mem_nhds (max_lt ha one_lt_golden)
  obtain ⟨c,hl,ha',hez,hep⟩ := (eleft.and (((eabove.and (ez.and epall)).filter_mono nhdsWithin_le_nhds))).exists
  exact ⟨c,ha',hl,fun i => ⟨(dyadic_bounds i.val).1,hez i⟩,hep⟩

private lemma pair_total (n : ℕ) (u : ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then u else 0) = u*(n:ℝ)*((n:ℝ)-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp_rw [Fin.sum_univ_succ]
    simp only [lt_self_iff_false, if_false, Fin.succ_pos, if_true, Fin.not_lt_zero, zero_add,
      Fin.succ_lt_succ_iff, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ih]
    push_cast
    ring

private def bottomWeights (n : ℕ) : Fin (n+1) → ℝ :=
  Fin.cases (1/2) (fun _ => 1/(2*(n:ℝ)))

private lemma bottom_mass {n : ℕ} (hn : 0 < n) : Mass (bottomWeights n) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  constructor
  · intro i
    refine Fin.cases (by norm_num [bottomWeights]) (fun j => ?_) i
    simp [bottomWeights]
  · rw [Fin.sum_univ_succ]
    simp [bottomWeights]
    field_simp
    ring

/-- For arbitrarily large n, a strict dyadic ladder with n higher labels
is admissible arbitrarily close to the golden ratio from below. -/
theorem dyadic_lower_near (a : ℝ) (ha : a < golden) (n : ℕ) (hn : 0 < n) :
    ∃ c, max a 1 < c ∧ c < golden ∧ 1/4 - 1/(8*(n:ℝ)) ≤ beta c := by
  classical
  obtain ⟨c,hca,hcφ,hcfg,hwin⟩ := finite_dyadic ha n
  let x (i : Fin (n+1)) := dyadicLevel i.val
  let w := bottomWeights n
  have mass := bottom_mass hn
  have h0 : x 0 = 1 := by simp [x,dyadicLevel]
  let L (i j k : Fin (n+1)) : ℝ :=
    if (i=0 ∧ j<k) ∨ (j=0 ∧ i<k) then w i*w j*w k else 0
  have hbound (i j k : Fin (n+1)) : L i j k ≤
      if Win c x i j k then w i*w j*w k else 0 := by
    by_cases h : (i=0 ∧ j<k) ∨ (j=0 ∧ i<k)
    · have hw : Win c x i j k := by
        rcases h with ⟨rfl,hjk⟩ | ⟨rfl,hik⟩
        · change x 0 + x j < c * x k
          simpa [h0,x] using hwin j k hjk
        · change x i + x 0 < c * x k
          rw [h0,add_comm]
          exact hwin i k hik
      simp [L,h,hw]
    · have hp := mul_nonneg (mul_nonneg (mass.1 i) (mass.1 j)) (mass.1 k)
      simp only [L,if_neg h]
      split_ifs <;> first | exact hp | exact le_rfl
  have he : (∑ i, ∑ j, ∑ k, L i j k) = 1/4 - 1/(8*(n:ℝ)) := by
    simp only [Fin.sum_univ_succ,L,Fin.succ_pos,Fin.succ_ne_zero,
      lt_self_iff_false,Fin.not_lt_zero,Fin.succ_lt_succ_iff,true_and,false_and,
      false_or,or_false,or_self,if_true,if_false,Finset.sum_const_zero,add_zero,zero_add,
      w,bottomWeights,Fin.cases_zero,Fin.cases_succ]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,pair_total]
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    field_simp
    ring
  refine ⟨c,hca,hcφ,?_⟩
  calc
    _ = ∑ i, ∑ j, ∑ k, L i j k := he.symm
    _ ≤ score c x w := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      Finset.sum_le_sum fun k _ => hbound i j k
    _ ≤ beta c := le_csSup (bdd_values c) ⟨_,x,w,hcfg,mass,rfl⟩

theorem eventually_above_below_quarter {b : ℝ} (hb : b < 1/4) :
    ∀ᶠ c in 𝓝[<] golden, b < beta c := by
  let g : ℝ := 1/4 - b
  have hg : 0 < g := sub_pos.mpr hb
  obtain ⟨n,hn⟩ := exists_nat_gt (1/(8*g))
  have hn' : 0 < (n : ℝ) := lt_trans (by positivity) hn
  have hratio : 1/(8*(n : ℝ)) < g := by
    apply (div_lt_iff₀ (by positivity)).2
    have hh := (div_lt_iff₀ (by positivity : 0 < 8*g)).1 hn
    linarith
  obtain ⟨c,hc,hl,hv⟩ := dyadic_lower_near 1 one_lt_golden n (by exact_mod_cast hn')
  have ha : 1 < c := (le_max_right ..).trans_lt hc
  have ev : ∀ᶠ d in 𝓝[<] golden, c < d := (lt_mem_nhds hl).filter_mono nhdsWithin_le_nhds
  filter_upwards [ev] with d hd
  exact lt_of_lt_of_le (by dsimp [g] at hratio; linarith) (hv.trans (beta_mono ha hd.le))

#print axioms eventually_above_below_quarter
end OneScale
