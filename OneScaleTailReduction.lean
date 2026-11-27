import OneScaleLocations

open Finset Set Filter
open scoped Topology BigOperators

namespace OneScale

/-- Canonical levels from the ordinary ladder and the single branching ladder. -/
def CanonicalLevel (c t : ℝ) : Prop :=
  (∃ n, t = ladderValue c n) ∨ ∃ j, t = branchValue c j

/-- The closed comparison at a canonical configuration. -/
def WeakWin {α : Type*} (c : ℝ) (z : α → ℝ) (i j k : α) : Prop :=
  z i + z j ≤ c * z k

noncomputable def weakScore {α : Type*} [Fintype α] (c : ℝ) (z w : α → ℝ) : ℝ := by
  classical exact ∑ i, ∑ j, ∑ k, if WeakWin c z i j k then w i*w j*w k else 0

/-- Rounding down to the greatest feasible tree value preserves every closed comparison. -/
theorem canonical_round {c : ℝ} (hc : 1<c) (hg : c<golden) {α : Type*}
    (x : α → ℝ) (hx : Cfg c x) :
    ∃ z : α → ℝ, Cfg c z ∧ (∀ i, CanonicalLevel c (z i)) ∧
      ∀ i j k, WeakWin c x i j k → WeakWin c z i j k := by
  classical
  have hc0 : 0<c := by linarith
  have hgold := (before_golden hc).mp hg
  have hc2 : c≤2 := by nlinarith [sq_nonneg (c-1)]
  obtain ⟨H,hH⟩ := ThresholdTree.bounded_menu hc hgold
  let M := ThresholdTree.menu H
  have hl : ThresholdTree.leaf ∈ M := (ThresholdTree.mem_menu_iff _ _).mpr (Nat.zero_le _)
  have select (i : α) : ∃ t ∈ M, t.value c ≤ x i ∧
      ∀ u ∈ M, u.value c ≤ x i → u.value c ≤ t.value c := by
    let L := M.filter fun t => t.value c ≤ x i
    have hn : L.Nonempty := ⟨.leaf,mem_filter.mpr ⟨hl,(hx i).1⟩⟩
    obtain ⟨t,ht,hm⟩ := Finset.exists_max_image L (ThresholdTree.value c) hn
    exact ⟨t,(mem_filter.mp ht).1,(mem_filter.mp ht).2,fun u hu hux => hm u (mem_filter.mpr ⟨hu,hux⟩)⟩
  choose t _ htx hmax using select
  let z (i : α) := (t i).value c
  have hz : Cfg c z := fun i => ⟨ThresholdTree.one_le_value hc0 hc2 _,(htx i).trans_lt (hx i).2⟩
  refine ⟨z,hz,fun i => ThresholdTree.feasible_value hc hgold (t i) (hz i).2.le,?_⟩
  intro i j k h
  let par := ThresholdTree.node (t i) (t j)
  have hpar : par.value c ≤ x k := by
    apply (div_le_iff₀ hc0).mpr
    change x i+x j ≤ c*x k at h
    linarith [htx i,htx j]
  have hm := hmax k par (hH c hc le_rfl par (hpar.trans (hx k).2.le)) hpar
  have h' := (div_le_iff₀ hc0).mp hm
  simpa [WeakWin,z,mul_comm] using h'

/-- A small dilation about one realizes every closed comparison as a strict one,
while preserving every losing comparison. -/
theorem realize_weak_pattern {α : Type*} [Fintype α] {c : ℝ} (hc : c<2)
    (z : α → ℝ) (hz : Cfg c z) :
    ∃ x : α → ℝ, Cfg c x ∧ ∀ i j k, Win c x i j k ↔ WeakWin c z i j k := by
  let f (K v : ℝ) := 1+K*(v-1)
  have fone (v : ℝ) : f 1 v = v := by dsimp [f]; ring
  have cont (v : ℝ) : ContinuousAt (fun K => f K v) 1 := by dsimp [f]; fun_prop
  have bounded : ∀ᶠ K in 𝓝 (1:ℝ), ∀ i, f K (z i)<c := by
    apply eventually_all.mpr
    intro i
    exact (cont _).eventually_lt_const (by simpa [fone] using (hz i).2)
  have lose : ∀ᶠ K in 𝓝 (1:ℝ), ∀ i j k, ¬WeakWin c z i j k →
      c*f K (z k)<f K (z i)+f K (z j) := by
    apply eventually_all.mpr; intro i
    apply eventually_all.mpr; intro j
    apply eventually_all.mpr; intro k
    by_cases h : WeakWin c z i j k
    · exact Eventually.of_forall fun _ hn => (hn h).elim
    · have hlt : c*z k<z i+z j := lt_of_not_ge h
      have ea := ((continuousAt_const.mul (cont (z k))).tendsto).eventually_lt
        (((cont (z i)).add (cont (z j))).tendsto) (by simpa [fone] using hlt)
      exact ea.mono fun K hK _ => hK
  have high : ∀ᶠ K in 𝓝[>] (1:ℝ), 1<K := self_mem_nhdsWithin
  obtain ⟨K,hK,hb,hl⟩ := (high.and
    ((bounded.and lose).filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨fun i => f K (z i),fun i => ⟨?_,hb i⟩,?_⟩
  · dsimp [f]
    nlinarith [mul_nonneg (by linarith : 0≤K) (sub_nonneg.mpr (hz i).1)]
  · intro i j k
    constructor
    · intro hw
      by_contra hn
      exact (not_lt_of_ge (hl i j k hn).le) hw
    · intro hw
      change z i+z j≤c*z k at hw
      change f K (z i)+f K (z j)<c*f K (z k)
      dsimp [f]
      nlinarith [mul_nonneg (by linarith : 0≤K) (sub_nonneg.mpr hw),
        mul_pos (sub_pos.mpr hK) (sub_pos.mpr hc)]

private theorem score_le_weak_of_wins {α : Type*} [Fintype α] {c : ℝ} {x z w : α → ℝ}
    (hw : Mass w) (h : ∀ i j k, Win c x i j k → WeakWin c z i j k) :
    score c x w ≤ weakScore c z w := by
  classical
  unfold score weakScore
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
  by_cases ha : Win c x i j k
  · simp [ha,h i j k ha]
  · by_cases hb : WeakWin c z i j k <;> simp [ha,hb,mul_nonneg,hw.1]

private theorem score_eq_weak_of_pattern {α : Type*} [Fintype α] {c : ℝ} {x z w : α → ℝ}
    (h : ∀ i j k, Win c x i j k ↔ WeakWin c z i j k) :
    score c x w = weakScore c z w := by classical simp [score,weakScore,h]

/-- All closed-comparison scores on admissible finite supports are attained as
ordinary strict scores after a sufficiently small change of coordinates. -/
theorem weakScore_mem_values {n : ℕ} {c : ℝ} (hc : c<2) {z w : Fin n → ℝ}
    (hz : Cfg c z) (hw : Mass w) : weakScore c z w ∈ values c := by
  obtain ⟨x,hx,h⟩ := realize_weak_pattern hc z hz
  exact ⟨n,x,w,hx,hw,score_eq_weak_of_pattern h⟩

/-- Actual maximum over the admissible ordinary and branching levels at c. -/
theorem beta_isGreatest_canonical {c : ℝ} (hc : 1<c) (hg : c<golden) :
    IsGreatest {b : ℝ | ∃ (n : ℕ) (z w : Fin n → ℝ), Cfg c z ∧ Mass w ∧
      (∀ i, CanonicalLevel c (z i)) ∧ weakScore c z w = b} (beta c) := by
  have hg' := (before_golden hc).mp hg
  have hc2 : c<2 := by nlinarith [sq_nonneg (c-1)]
  obtain ⟨B,hB,hF⟩ := uniform_factorization hc hg'
  obtain ⟨n,x,w,hx,hw,hβ⟩ := (beta_attained_menu hc hB (hF c hc le_rfl)).2
  obtain ⟨z,hz,hcan,h⟩ := canonical_round hc hg x hx
  have hlow : score c x w ≤ weakScore c z w :=
    score_le_weak_of_wins hw (fun i j k hij => h i j k (LT.lt.le hij))
  have hupp := le_csSup (bdd_values c) (weakScore_mem_values hc2 hz hw)
  refine ⟨⟨n,z,w,hz,hw,hcan,le_antisymm hupp (hβ ▸ hlow)⟩,?_⟩
  rintro _ ⟨m,z',w',hz',hw',_,rfl⟩
  exact le_csSup (bdd_values c) (weakScore_mem_values hc2 hz' hw')

private def ordinaryTree : ℕ → ThresholdTree
  | 0 => .leaf
  | n+1 => .node .leaf (ordinaryTree n)

private def branchingTree : ℕ → ThresholdTree
  | 0 => .node (.node .leaf .leaf) (.node .leaf .leaf)
  | n+1 => .node .leaf (branchingTree n)

private theorem ordinaryTree_value (c : ℝ) (n : ℕ) :
    (ordinaryTree n).value c = ladderValue c n := by
  induction n with
  | zero => rfl
  | succ n hi => simp [ordinaryTree,ThresholdTree.value,ladderValue,hi]

private theorem branchingTree_value (c : ℝ) (n : ℕ) :
    (branchingTree n).value c = branchValue c n := by
  induction n with
  | zero => simp [branchingTree,ThresholdTree.value,branchValue]; ring
  | succ n hi => simp [branchingTree,ThresholdTree.value,branchValue,hi]

/-- Every canonical coordinate is an explicit binary tree value. -/
theorem canonicalLevel_iff_tree {c t : ℝ} (hc : 1<c) (hg : c<golden) (ht : t≤c) :
    CanonicalLevel c t ↔ ∃ T : ThresholdTree, t = T.value c := by
  constructor
  · rintro (⟨n,rfl⟩|⟨j,rfl⟩)
    · exact ⟨_,(ordinaryTree_value c n).symm⟩
    · exact ⟨_,(branchingTree_value c j).symm⟩
  · rintro ⟨T,rfl⟩
    exact ThresholdTree.feasible_value hc ((before_golden hc).mp hg) T ht

private theorem weakScore_push {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq γ]
    {c : ℝ} (hc : c<2) (e : α → γ) {z : γ → ℝ} (hz : Cfg c z) (w : α → ℝ) :
    weakScore c z (push e w) = weakScore c (z ∘ e) w := by
  obtain ⟨x,_,h⟩ := realize_weak_pattern hc z hz
  rw [← score_eq_weak_of_pattern h,score_push]
  exact score_eq_weak_of_pattern (fun i j k => h (e i) (e j) (e k))

private theorem weakScore_le_beta {α : Type*} [Fintype α] {c : ℝ} (hc : c<2)
    {x w : α → ℝ} (hx : Cfg c x) (hw : Mass w) : weakScore c x w ≤ beta c := by
  let e := Fintype.equivFin α
  let z := x ∘ e.symm
  have hz : Cfg c z := fun i => hx (e.symm i)
  have hcomp : z ∘ e = x := by funext i; simp [z]
  have h := weakScore_push hc e hz w
  rw [hcomp] at h
  rw [← h]
  exact le_csSup (bdd_values c) (weakScore_mem_values hc hz (mass_push e hw))

/-- A single finite support consisting of *all* active ladder coordinates gives
an exact cubic program. There is one mass per distinct coordinate. -/
theorem beta_fixed_canonical_menu {c : ℝ} (hc : 1<c) (hg : c<golden) :
    ∃ S : Finset ℝ, (∀ t, t∈S ↔ CanonicalLevel c t ∧ t<c) ∧
      ∃ w : S → ℝ, Mass w ∧ weakScore c Subtype.val w = beta c ∧
        ∀ u : S → ℝ, Mass u → weakScore c Subtype.val u ≤ beta c := by
  classical
  have hg' := (before_golden hc).mp hg
  have hc2 : c<2 := by nlinarith [sq_nonneg (c-1)]
  obtain ⟨H,hH⟩ := ThresholdTree.bounded_menu hc hg'
  let S := ((ThresholdTree.menu H).image (ThresholdTree.value c)).filter (· < c)
  have spec (t : ℝ) : t∈S ↔ CanonicalLevel c t ∧ t<c := by
    constructor
    · intro h
      obtain ⟨hm,ht⟩ := mem_filter.mp h
      obtain ⟨T,_,rfl⟩ := mem_image.mp hm
      exact ⟨(canonicalLevel_iff_tree hc hg ht.le).mpr ⟨T,rfl⟩,ht⟩
    · rintro ⟨h,ht⟩
      obtain ⟨T,rfl⟩ := (canonicalLevel_iff_tree hc hg ht.le).mp h
      exact mem_filter.mpr ⟨mem_image.mpr ⟨T,hH c hc le_rfl _ ht.le,rfl⟩,ht⟩
  have hS : Cfg c (Subtype.val : S → ℝ) := by
    intro t
    obtain ⟨h,ht⟩ := (spec t).mp t.property
    obtain ⟨T,hT⟩ := (canonicalLevel_iff_tree hc hg ht.le).mp h
    exact ⟨hT ▸ ThresholdTree.one_le_value (by linarith) hc2.le T,ht⟩
  obtain ⟨n,x,w,hx,hw,hxcan,hβ⟩ := (beta_isGreatest_canonical hc hg).1
  let idx (i : Fin n) : S := ⟨x i,(spec _).mpr ⟨hxcan i,(hx i).2⟩⟩
  refine ⟨S,spec,push idx w,mass_push idx hw,?_,fun u hu => weakScore_le_beta hc2 hS hu⟩
  exact (weakScore_push hc2 idx hS w).trans hβ

/-- The ordinary ladder is strictly increasing throughout the subcritical regime. -/
theorem ladderValue_strictMono {c : ℝ} (hc : 1<c) (hg : c<golden) : StrictMono (ladderValue c) := by
  have hg' := (before_golden hc).mp hg
  have hc0 : 0<c := by linarith
  have hc2 : c<2 := by nlinarith [sq_nonneg (c-1)]
  apply strictMono_nat_of_lt_succ
  intro n
  induction n with
  | zero => change 1<(1+1)/c; exact (lt_div_iff₀ hc0).mpr (by linarith)
  | succ n ih => exact div_lt_div_of_pos_right (add_lt_add_left ih 1) hc0

/-- The two ladders interleave strictly from the third ordinary rung on. -/
theorem canonical_interlace {c : ℝ} (hc : 1<c) (hg : c<golden) (j : ℕ) :
    ladderValue c (j+3)<branchValue c j ∧ branchValue c j<ladderValue c (j+4) := by
  have hg' := (before_golden hc).mp hg
  have hc0 : 0<c := by linarith
  have hc2 : c<2 := by nlinarith [sq_nonneg (c-1)]
  induction j with
  | zero =>
    have h3 : (branchValue c 0-ladderValue c 3)*c^3=(c-1)*(2-c) := by
      norm_num [branchValue,ladderValue]; field_simp; ring
    have h4 : (ladderValue c 4-branchValue c 0)*c^4=(2-c)*(c+1-c*c) := by
      norm_num [branchValue,ladderValue]; field_simp; ring
    constructor
    · exact sub_pos.mp (pos_of_mul_pos_left (h3 ▸ mul_pos (sub_pos.mpr hc) (sub_pos.mpr hc2)) (by positivity))
    · exact sub_pos.mp (pos_of_mul_pos_left (h4 ▸ mul_pos (sub_pos.mpr hc2) (sub_pos.mpr hg')) (by positivity))
  | succ j ih =>
    exact ⟨div_lt_div_of_pos_right (add_lt_add_left ih.1 1) hc0,
      div_lt_div_of_pos_right (add_lt_add_left ih.2 1) hc0⟩

private theorem canonical_trichotomy {c t : ℝ} (hc : 1<c) (hg : c<golden)
    (ht : CanonicalLevel c t) : t=1 ∨ t=ladderValue c 1 ∨ ladderValue c 2≤t := by
  have hm := ladderValue_strictMono hc hg
  rcases ht with ⟨n,rfl⟩|⟨j,rfl⟩
  · rcases n with _|n
    · exact Or.inl rfl
    rcases n with _|n
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (hm.monotone (by omega)))
  · exact Or.inr (Or.inr ((hm.monotone (show 2 ≤ j+3 by omega)).trans (canonical_interlace hc hg j).1.le))

/-- Complete list of closed winning triples. A pair avoiding the bottom
level must consist of two first rungs, and its target must reach the first fork. -/
theorem canonical_edge_iff {c x y z : ℝ} (hc : 1<c) (hg : c<golden)
    (hx : CanonicalLevel c x) (hy : CanonicalLevel c y) (hz : z<c) :
    x+y≤c*z ↔ (x=1 ∧ (1+y)/c≤z) ∨ (y=1 ∧ (1+x)/c≤z) ∨
      (x=ladderValue c 1 ∧ y=ladderValue c 1 ∧ branchValue c 0≤z) := by
  have hc0 : 0<c := by linarith
  have hg' := (before_golden hc).mp hg
  have h1 : ladderValue c 1 = 2/c := by norm_num [ladderValue]
  have h2 : ladderValue c 2 = (1+2/c)/c := by norm_num [ladderValue]
  have hb : branchValue c 0 = (ladderValue c 1 + ladderValue c 1)/c := by rw [h1]; dsimp [branchValue]; ring
  have hgap : c*c < ladderValue c 1 + ladderValue c 2 := by
    rw [h1,h2]
    have hp : 0<c*c+c+2 := by positivity
    have h4 : c^4<3*c+2 := by nlinarith [mul_neg_of_neg_of_pos (sub_neg.mpr hg') hp]
    have ht : (2/c+(1+2/c)/c)*(c*c) = 3*c+2 := by field_simp; ring
    by_contra! h
    have hh := mul_le_mul_of_nonneg_right h (mul_nonneg hc0.le hc0.le)
    nlinarith
  constructor
  · intro h
    by_cases hX : x=1
    · exact Or.inl ⟨hX,(div_le_iff₀ hc0).mpr (by rw [hX] at h; linarith)⟩
    by_cases hY : y=1
    · exact Or.inr (Or.inl ⟨hY,(div_le_iff₀ hc0).mpr (by rw [hY] at h; linarith)⟩)
    have hX' := (canonical_trichotomy hc hg hx).resolve_left hX
    have hY' := (canonical_trichotomy hc hg hy).resolve_left hY
    have h12 := (ladderValue_strictMono hc hg) (show (1:ℕ)<2 by decide)
    have hbnd := mul_lt_mul_of_pos_left hz hc0
    have X : x=ladderValue c 1 := by rcases hX' with H|H; exact H; rcases hY' with E|E <;> linarith
    have Y : y=ladderValue c 1 := by rcases hY' with H|H; exact H; linarith
    right; right
    exact ⟨X,Y,hb ▸ (div_le_iff₀ hc0).mpr (by linarith)⟩
  · rintro (⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,rfl,h⟩)
    · linarith [(div_le_iff₀ hc0).mp h]
    · linarith [(div_le_iff₀ hc0).mp h]
    · rw [hb] at h
      linarith [(div_le_iff₀ hc0).mp h]

#print axioms beta_fixed_canonical_menu
#print axioms canonical_edge_iff

end OneScale
