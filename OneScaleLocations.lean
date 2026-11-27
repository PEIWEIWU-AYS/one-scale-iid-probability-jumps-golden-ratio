import OneScaleTrees
import OneScaleJumps

open Finset Set Filter
open scoped Topology BigOperators

namespace OneScale

/-- A comparison tree ending at a specified atom; its internal nodes may use
only winning relations of the given finite configuration. -/
private inductive Recipe {α : Type*} (s : ℝ) (x : α → ℝ) : α → ThresholdTree → Prop
  | base (i : α) : Recipe s x i .leaf
  | join {i j k : α} {u v : ThresholdTree} (hu : Recipe s x i u)
      (hv : Recipe s x j v) (h : Win s x i j k) : Recipe s x k (.node u v)

private lemma recipe_le {α : Type*} {s : ℝ} {x : α → ℝ} {i : α} {u : ThresholdTree}
    (hs : 0<s) (hx : Cfg s x) (h : Recipe s x i u) : u.value s ≤ x i := by
  induction h with
  | base i => exact (hx i).1
  | @join i j k u v hu hv h ia ib =>
    apply (div_le_iff₀ hs).2
    change x i + x j < s*x k at h
    linarith

/-- Once the signs of all relevant root inequalities are fixed, every winning
system at the higher coefficient has a realization at the lower one. -/
private lemma replay {c s l C : ℝ} (hl : 1<l) (hlc : l<c) (hs : 1<s)
    (hsC : s≤C) (hl2 : l≤2) (H : ℕ)
    (hH : ∀ u : ThresholdTree, u.value s ≤ C → u ∈ ThresholdTree.menu H)
    (hsign : ∀ u ∈ ThresholdTree.menu H, u.value s<s → u.value l<c)
    {α : Type*} [Fintype α] (x : α → ℝ) (hx : Cfg s x) :
    ∃ y : α → ℝ, Cfg c y ∧ ∀ i j k, Win s x i j k → Win c y i j k := by
  classical
  let M := ThresholdTree.menu H
  have hrecipe {i : α} {u : ThresholdTree} (h : Recipe s x i u) : u.value s < s :=
    (recipe_le (by linarith : 0<s) hx h).trans_lt (hx i).2
  have get (i : α) : ∃ t ∈ M, Recipe s x i t ∧
      ∀ u ∈ M, Recipe s x i u → u.value l ≤ t.value l := by
    let S := M.filter (fun u => Recipe s x i u)
    have hbase : Recipe s x i .leaf := Recipe.base i
    have hit : S.Nonempty := ⟨.leaf,Finset.mem_filter.mpr
      ⟨hH _ ((hrecipe hbase).le.trans hsC),hbase⟩⟩
    obtain ⟨t,ht,hm⟩ := Finset.exists_max_image S (ThresholdTree.value l) hit
    exact ⟨t,(Finset.mem_filter.mp ht).1,(Finset.mem_filter.mp ht).2,
      fun u hu hr => hm u (Finset.mem_filter.mpr ⟨hu,hr⟩)⟩
  choose tree hmem hvalid hmax using get
  let y (i : α) := (tree i).value l
  have hy (i : α) : 1 ≤ y i :=
    ThresholdTree.one_le_value (by linarith) hl2 (tree i)
  refine ⟨y,fun i => ⟨hy i,hsign (tree i) (hmem i) (hrecipe (hvalid i))⟩,?_⟩
  intro i j k h
  have hr := Recipe.join (hvalid i) (hvalid j) h
  have ht := hmax k _ (hH _ ((hrecipe hr).le.trans hsC)) hr
  change (y i+y j)/l ≤ y k at ht
  have hprod := (div_le_iff₀ (by linarith : 0<l)).mp ht
  have hh := mul_lt_mul_of_pos_right hlc (show 0<y k by linarith [hy k])
  change y i+y j < c*y k
  linarith

/-- Every genuine one-scale jump below the golden ratio belongs to one of
the two ladder families of Zaytsev and Bellec. -/
theorem jump_location {c J : ℝ} (hc : 1<c) (hg : c<golden) (hJ : 0<J)
    (hj : IidJumpSpectra.RightJump beta c J) : LadderCandidate c := by
  classical
  by_contra hn
  obtain ⟨C,hcC,hCg⟩ := exists_between hg
  have hC1 := hc.trans hcC
  obtain ⟨H,hH⟩ := ThresholdTree.bounded_menu hC1 ((before_golden hC1).mp hCg)
  let M := ThresholdTree.menu H
  have hcn : c≠0 := by linarith
  have hnroot (t : M) : t.1.value c ≠ c := fun he =>
    hn (ThresholdTree.candidate_of_tree_root hc ((before_golden hc).mp hg) _ he)
  have low : ∀ᶠ l in 𝓝 c, ∀ t : M, t.1.value c<c → t.1.value l<c := by
    apply eventually_all.mpr
    intro t
    by_cases h : t.1.value c<c
    · exact ((ThresholdTree.value_continuousAt hcn t.1).eventually_lt_const h).mono
        fun s hs _ => hs
    · exact Eventually.of_forall fun _ hh => (h hh).elim
  have high : ∀ᶠ s in 𝓝 c, ∀ t : M, t.1.value s<s → t.1.value c<c := by
    apply eventually_all.mpr
    intro t
    by_cases h : t.1.value c<c
    · exact Eventually.of_forall fun _ _ => h
    · have hg' : c<t.1.value c := lt_of_le_of_ne (not_lt.mp h) (Ne.symm (hnroot t))
      have hh : ∀ᶠ s in 𝓝 c, s<t.1.value s :=
        (continuousAt_id.tendsto).eventually_lt (ThresholdTree.value_continuousAt hcn t.1).tendsto hg'
      exact hh.mono fun s hs hh' => (lt_asymm hs hh').elim
  have leftN : ∀ᶠ l in 𝓝[<] c, l<c := self_mem_nhdsWithin
  have rightN : ∀ᶠ s in 𝓝[>] c, c<s := self_mem_nhdsWithin
  obtain ⟨l,hlc,hl,hlow⟩ := (leftN.and
    (((eventually_gt_nhds hc).and low).filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨s,hcs,hsC,hhigh⟩ := (rightN.and
    (((eventually_lt_nhds hcC).and high).filter_mono nhdsWithin_le_nhds)).exists
  have h2 : l≤2 := by
    have := (before_golden hc).mp hg
    nlinarith [sq_nonneg (c-1)]
  have hβ : beta s ≤ beta c := by
    apply csSup_le (values_nonempty (hc.trans hcs))
    rintro a ⟨n,x,w,hx,hw,rfl⟩
    obtain ⟨y,hy,hretain⟩ := replay hl hlc (hc.trans hcs) hsC.le h2 H
      (hH s (hc.trans hcs) hsC.le)
      (fun t ht hv => hlow ⟨t,ht⟩ (hhigh ⟨t,ht⟩ hv)) x hx
    exact (score_mono_wins hw hretain).trans (le_csSup (bdd_values c)
      ⟨n,y,w,hy,hw,rfl⟩)
  linarith [hj s hcs]

/-- Infinitely many of the two explicit candidate families are actual
one-scale jump locations in every left neighborhood of the golden ratio. -/
theorem infinitely_many_ladder_jumps {a : ℝ} (ha : a<golden) :
    {b : ℝ | a<b ∧ b<golden ∧ LadderCandidate b ∧
      ∃ J : ℝ, 0<J ∧ IidJumpSpectra.RightJump beta b J}.Infinite := by
  apply (infinitely_many_oneScale_jumps (max_lt ha one_lt_golden)).mono
  intro b h
  obtain ⟨hb,hg,J,hJ,hjump⟩ := h
  exact ⟨(le_max_left a 1).trans_lt hb,hg,
    jump_location ((le_max_right a 1).trans_lt hb) hg hJ hjump,J,hJ,hjump⟩

#print axioms jump_location
#print axioms infinitely_many_ladder_jumps

end OneScale
