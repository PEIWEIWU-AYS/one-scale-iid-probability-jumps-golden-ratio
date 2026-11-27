import OneScaleMenu
import OneScaleCompression
import OneScaleSplit
import JumpTransfer
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.IntermediateValue

open Filter Set Finset
open scoped Topology BigOperators

namespace OneScale

noncomputable def golden : ℝ := (1 + Real.sqrt 5)/2

theorem one_lt_golden : (1 : ℝ) < golden := by
  have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  dsimp [golden]
  nlinarith [Real.sqrt_nonneg 5]

private theorem golden_eq : golden * golden = golden + 1 := by
  have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  dsimp [golden]
  nlinarith

theorem before_golden {c : ℝ} (hc : 1 < c) : c < golden ↔ c*c < c+1 := by
  have hpos : 0 < c+golden-1 := by linarith [one_lt_golden]
  constructor
  · intro h
    nlinarith [mul_pos (sub_pos.mpr h) hpos,golden_eq]
  · intro h
    by_contra! hf
    nlinarith [mul_nonneg (sub_nonneg.mpr hf) hpos.le,golden_eq]

private theorem bounded_menu {C : ℝ} (hc : 1 < C) (hφ : C < golden) :
    ∃ p : Finset ℝ, ∀ c, 1 < c → c ≤ C → beta c ∈ p ∧ beta c ∈ values c := by
  obtain ⟨B,hB,hf⟩ := uniform_factorization hc ((before_golden hc).mp hφ)
  exact ⟨menu B, fun c hc' h => beta_attained_menu hc' hB (hf c hc' h)⟩

private theorem stable_to_left {c : ℝ} (hc : 1 < c) (hφ : c < golden) :
    ∃ d, 1 < d ∧ d < c ∧ beta d = beta c := by
  classical
  obtain ⟨_,hm⟩ := bounded_menu hc hφ
  obtain ⟨n,x,w,hx,hw,hs⟩ := (hm c hc le_rfl).2
  have hsupport : ∀ᶠ s in 𝓝 c, ∀ i, x i < s :=
    eventually_all.mpr (fun i => eventually_gt_nhds (hx i).2)
  have hwin : ∀ᶠ s in 𝓝 c, ∀ i j k, Win c x i j k → Win s x i j k := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k => ?_
    by_cases h : Win c x i j k
    · have hcont : ContinuousAt (fun s : ℝ => s*x k) c := by fun_prop
      exact (hcont.tendsto.eventually_const_lt h).mono (fun _ hl _ => hl)
    · exact Eventually.of_forall (fun _ hh => (h hh).elim)
  have all := ((eventually_gt_nhds hc).and (hsupport.and hwin)).filter_mono
    (nhdsWithin_le_nhds : 𝓝[<] c ≤ 𝓝 c)
  have hl : ∀ᶠ s in 𝓝[<] c, s < c := self_mem_nhdsWithin
  obtain ⟨s,hsc,hs1,hsx,hsw⟩ := (hl.and all).exists
  refine ⟨s,hs1,hsc,le_antisymm (beta_mono hs1 hsc.le) ?_⟩
  rw [←hs]
  exact (score_mono_wins hw hsw).trans (le_csSup (bdd_values s)
    ⟨n,x,w,fun i => ⟨(hx i).1, hsx i⟩,hw,rfl⟩)

private theorem beta_nonneg {c : ℝ} (hc : 1 < c) : 0 ≤ beta c := by
  obtain ⟨z,n,x,w,_,hw,hs⟩ := values_nonempty hc
  have hscore : 0 ≤ score c x w := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
      split_ifs <;> simp [mul_nonneg,hw.1]
  exact (hs ▸ hscore).trans (le_csSup (bdd_values c)
    (show z ∈ values c from by subst z; exact ⟨n,x,w,by assumption,hw,rfl⟩))

private theorem beta_zero {c : ℝ} (hc : c ≤ 1) : beta c = 0 := by
  have hempty : values c = ∅ := by
    apply Set.eq_empty_of_forall_not_mem
    rintro _ ⟨n,x,w,hx,hw,_⟩
    cases n with
    | zero => simpa using hw.2
    | succ n =>
      have h := hx 0
      linarith [h.1,h.2]
  simp [beta,hempty]

theorem beta_monotone : Monotone beta := by
  intro c d hcd
  by_cases hc : 1 < c
  · exact beta_mono hc hcd
  · rw [beta_zero (le_of_not_gt hc)]
    by_cases hd : 1 < d
    · exact beta_nonneg hd
    · rw [beta_zero (le_of_not_gt hd)]

private theorem right_gap {b : ℝ} (hb : 1 < b) (hφ : b < golden)
    (hd : ¬ ContinuousAt beta b) : ∃ J, 0 < J ∧ IidJumpSpectra.RightJump beta b J := by
  let mono := beta_monotone
  obtain ⟨s,_,hs,hsb⟩ := stable_to_left hb hφ
  have hl : Function.leftLim beta b = beta b := by
    apply le_antisymm (mono.leftLim_le le_rfl)
    rw [←hsb]
    exact mono.le_leftLim hs
  have hn : Function.leftLim beta b ≠ Function.rightLim beta b :=
    fun h => hd (mono.continuousAt_iff_leftLim_eq_rightLim.mpr h)
  rw [hl] at hn
  have hg := lt_of_le_of_ne (mono.le_rightLim (le_refl b)) hn
  exact ⟨_,sub_pos.mpr hg,fun u h => by
    change beta b + (Function.rightLim beta b-beta b) ≤ beta u
    linarith [mono.rightLim_le h]⟩

/-- A single positive increase before the golden ratio forces an actual right
jump somewhere on that interval because the optimum there has finite range. -/
theorem jump_between {s t : ℝ} (hs : 1 < s) (hst : s < t) (ht : t < golden)
    (hinc : beta s < beta t) :
    ∃ b ∈ Set.Icc s t, ∃ J, 0 < J ∧ IidJumpSpectra.RightJump beta b J := by
  classical
  obtain ⟨menu,hmenu⟩ := bounded_menu (hs.trans hst) ht
  have hdisc : ∃ b ∈ Set.Icc s t, ¬ ContinuousAt beta b := by
    by_contra! hh
    have hcont : ContinuousOn beta (Set.Icc s t) := fun x hx => (hh x hx).continuousWithinAt
    have hsub : Set.Icc (beta s) (beta t) ⊆ (menu : Set ℝ) := by
      intro v hv
      obtain ⟨u,hu,rfl⟩ := intermediate_value_Icc hst.le hcont hv
      exact (hmenu u (hs.trans_le hu.1) hu.2).1
    exact Set.Icc_infinite hinc (menu.finite_toSet.subset hsub)
  obtain ⟨b,hb,hdisc⟩ := hdisc
  exact ⟨b,hb,right_gap (hs.trans_le hb.1) (hb.2.trans_lt ht) hdisc⟩


/-- Arbitrarily close to the golden ratio from below, the one-scale optimum
has a point with a strictly positive right-hand jump. -/
theorem cofinal_jumps {a : ℝ} (ha : a < golden) :
    ∃ b, max a 1 < b ∧ b < golden ∧
      ∃ J : ℝ, 0 < J ∧ IidJumpSpectra.RightJump beta b J := by
  obtain ⟨s,has,hsφ⟩ := exists_between (max_lt ha one_lt_golden)
  have hs : 1 < s := (le_max_right a 1).trans_lt has
  obtain ⟨_,hmenu⟩ := bounded_menu hs hsφ
  obtain ⟨t,v,hst,htφ,hv,hinc⟩ :=
    improve_value hs ((before_golden hs).mp hsφ) ((hmenu s hs le_rfl).2)
  have ht := (before_golden (hs.trans hst)).mpr htφ
  have hinc' := hinc.trans_le (le_csSup (bdd_values t) hv)
  obtain ⟨b,hb,hJ⟩ := jump_between hs hst ht hinc'
  exact ⟨b,has.trans_le hb.1,hb.2.trans_lt ht,hJ⟩

/-- Infinitely many distinct genuine jumps of the one-scale optimization
problem occur in each interval ending at the golden ratio from the left. -/
theorem infinitely_many_oneScale_jumps {a : ℝ} (ha : a < golden) :
    {b : ℝ | a < b ∧ b < golden ∧
      ∃ J : ℝ, 0 < J ∧ IidJumpSpectra.RightJump beta b J}.Infinite := by
  intro hf
  obtain ⟨b,hb,hφ,hJ⟩ := cofinal_jumps ha
  let s := {x : ℝ | a < x ∧ x < golden ∧
    ∃ J : ℝ, 0 < J ∧ IidJumpSpectra.RightJump beta x J}
  have hne : s.Nonempty := ⟨b,(le_max_left a 1).trans_lt hb,hφ,hJ⟩
  obtain ⟨y,hy,hmax⟩ := hf.exists_maximal_wrt id s hne
  obtain ⟨z,hz,hzφ,hzJ⟩ := cofinal_jumps hy.2.1
  have hyz := (le_max_left y 1).trans_lt hz
  have hzs : z ∈ s := ⟨hy.1.trans hyz,hzφ,hzJ⟩
  exact hyz.ne (hmax z hzs hyz.le)

#print axioms infinitely_many_oneScale_jumps
end OneScale
