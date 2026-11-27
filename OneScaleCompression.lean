import OneScaleModel

open Finset Filter
open scoped Topology

namespace OneScale

/-- A binary expression with all leaves equal to one. -/
inductive ThresholdTree where
  | leaf
  | node (left right : ThresholdTree)
  deriving DecidableEq

namespace ThresholdTree

noncomputable def value (d : ℝ) : ThresholdTree → ℝ
  | leaf => 1
  | node u v => (value d u + value d v) / d

def height : ThresholdTree → ℕ
  | leaf => 0
  | node u v => max (height u) (height v) + 1

def menu : ℕ → Finset ThresholdTree
  | 0 => {leaf}
  | n+1 => insert leaf (((menu n) ×ˢ (menu n)).image fun p => node p.1 p.2)

theorem mem_menu_iff (n : ℕ) (t : ThresholdTree) : t ∈ menu n ↔ t.height ≤ n := by
  induction n generalizing t with
  | zero => cases t <;> simp [menu, height]
  | succ n ih => cases t with
    | leaf => simp [menu, height]
    | node u v => simp [menu, height, ih]

theorem one_le_value {d : ℝ} (hd : 0 < d) (hd' : d ≤ 2) (t : ThresholdTree) :
    1 ≤ t.value d := by
  induction t with
  | leaf => simp [value]
  | node u v hu hv =>
    apply (le_div_iff₀ hd).2
    linarith

/-- Under the golden-ratio cutoff, each edge on a feasible tree consumes a
positive amount of the available interval. -/
private theorem height_bound {C d δ : ℝ} (hd : 1 < d) (hdC : d ≤ C) (hC : C < 2)
    (hδ : 0 < δ) (hδC : C*δ = 1 + C - C*C) (t : ThresholdTree)
    (ht : t.value d ≤ C) : 1 + (t.height : ℝ)*δ ≤ t.value d := by
  induction t with
  | leaf => simp [height, value]
  | node u v iu iv =>
    have hdp : 0 < d := by linarith
    have hCp : 0 < C := hdp.trans_le hdC
    have hu := one_le_value hdp (hdC.trans hC.le) u
    have hv := one_le_value hdp (hdC.trans hC.le) v
    have hs : value d u + value d v ≤ C*d := (div_le_iff₀ hdp).1 ht
    have hCd : C*d ≤ C*C := by gcongr
    have hδpos := mul_pos hCp hδ
    have huC : value d u ≤ C := by linarith
    have hvC : value d v ≤ C := by linarith
    have edge (a b : ℝ) (ha : 1 ≤ a) (hac : a ≤ C) (hb : 1 ≤ b) :
        a + δ ≤ (a+b)/d := by
      have hprod := mul_le_mul (sub_le_sub_right hdC 1) hac (by linarith : 0 ≤ a)
        (by linarith : 0 ≤ C-1)
      have herr := mul_le_mul_of_nonneg_right hdC hδ.le
      apply (le_div_iff₀ hdp).2
      nlinarith
    have eu := edge _ _ hu huC hv
    have ev := edge _ _ hv hvC hu
    rw [add_comm (v.value d) (u.value d)] at ev
    dsimp only [height, value]
    rcases le_total u.height v.height with h | h
    · rw [max_eq_right h, Nat.cast_add_one]
      linarith [iv hvC]
    · rw [max_eq_left h, Nat.cast_add_one]
      linarith [iu huC]

/-- One finite set of tree shapes is sufficient for all coefficients below C. -/
theorem bounded_menu {C : ℝ} (hC : 1 < C) (hgold : C*C < C+1) :
    ∃ H : ℕ, ∀ (d : ℝ), 1 < d → d ≤ C → ∀ t : ThresholdTree,
      t.value d ≤ C → t ∈ menu H := by
  let δ := (1+C-C*C)/C
  have hCp : 0 < C := by linarith
  have hδ : 0 < δ := div_pos (by linarith) hCp
  have heq : C*δ = 1+C-C*C := by dsimp [δ]; field_simp
  have ht : C < 2 := by nlinarith [sq_nonneg (C-1)]
  obtain ⟨H, hH⟩ := exists_nat_gt ((C-1)/δ)
  refine ⟨H, fun d hd hdC t hval => (mem_menu_iff _ _).2 ?_⟩
  have bound := height_bound hd hdC ht hδ heq t hval
  have hh := (div_lt_iff₀ hδ).1 hH
  exact_mod_cast (show (t.height:ℝ) ≤ H by nlinarith)

end ThresholdTree

private theorem coefficient_below {α : Type*} [Fintype α] {c : ℝ} (hc : 1 < c)
    (x : α → ℝ) : ∃ d : ℝ, 1 < d ∧ d < c ∧
      ∀ i j k, Win c x i j k → Win d x i j k := by
  have p (i j k : α) : ∀ᶠ d in 𝓝 c, Win c x i j k → Win d x i j k := by
    by_cases h : Win c x i j k
    · have hlt : x i + x j < c * x k := h
      have hct : ContinuousAt (fun d : ℝ => d * x k) c := by fun_prop
      exact (hct.eventually_const_lt hlt).mono (fun d he _ => he)
    · exact Eventually.of_forall (fun _ hw => (h hw).elim)
  have all : ∀ᶠ d in 𝓝 c, ∀ i j k, Win c x i j k → Win d x i j k :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k => p i j k
  have above : ∀ᶠ d in 𝓝 c, 1 < d := lt_mem_nhds hc
  have below : ∀ᶠ d in 𝓝[<] c, d < c := self_mem_nhdsWithin
  exact (((above.filter_mono nhdsWithin_le_nhds).and
    (below.and (all.filter_mono nhdsWithin_le_nhds))).exists)

/-- All strict winning comparisons survive compression to a uniformly bounded
number of support points. The bound depends only on the upper coefficient C. -/
theorem uniform_compression {C : ℝ} (hC : 1 < C) (hgold : C*C < C+1) :
    ∃ B : ℕ, ∀ {α : Type} [Fintype α] (c : ℝ), 1 < c → c ≤ C → ∀ x : α → ℝ,
      Cfg c x → ∃ y : α → ℝ, Cfg c y ∧ (univ.image y).card ≤ B ∧
        ∀ i j k, Win c x i j k → Win c y i j k := by
  classical
  obtain ⟨H,hH⟩ := ThresholdTree.bounded_menu hC hgold
  refine ⟨(ThresholdTree.menu H).card, ?_⟩
  intro α _ c hc hcC x hx
  obtain ⟨d, hd, hdc, hwin⟩ := coefficient_below hc x
  let M := ThresholdTree.menu H
  have hleaf : ThresholdTree.leaf ∈ M := (ThresholdTree.mem_menu_iff _ _).2 (Nat.zero_le _)
  have get (i : α) : ∃ t ∈ M, ThresholdTree.value d t ≤ x i ∧
      ∀ u ∈ M, ThresholdTree.value d u ≤ x i → ThresholdTree.value d u ≤ ThresholdTree.value d t := by
    let L := M.filter (fun t => t.value d ≤ x i)
    have hit : L.Nonempty := ⟨.leaf, Finset.mem_filter.mpr ⟨hleaf, (hx i).1⟩⟩
    obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image L (ThresholdTree.value d) hit
    exact ⟨t, (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2,
      fun u hu hu' => hmax u (Finset.mem_filter.mpr ⟨hu,hu'⟩)⟩
  choose t ht hxle hmax using get
  let y (i : α) := (t i).value d
  have hdC := hdc.le.trans hcC
  have hdp : 0 < d := by linarith
  have hCt : C < 2 := by nlinarith [sq_nonneg (C-1)]
  have hy (i : α) : 1 ≤ y i := ThresholdTree.one_le_value hdp (hdC.trans hCt.le) _
  refine ⟨y, (fun i => ⟨hy i, (hxle i).trans_lt (hx i).2⟩), ?_, ?_⟩
  · have hsub : univ.image y ⊆ M.image (ThresholdTree.value d) := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨t i, ht i, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  · intro i j k hw
    have hw' := hwin i j k hw
    change x i + x j < d * x k at hw'
    let parent := ThresholdTree.node (t i) (t j)
    have hpar : parent.value d ≤ x k := by
      apply (div_le_iff₀ hdp).2
      linarith [hxle i, hxle j]
    have hmem : parent ∈ M := hH d hd hdC parent (hpar.trans ((hx k).2.le.trans hcC))
    have hb := hmax k parent hmem hpar
    have hh := (div_le_iff₀ hdp).1 hb
    have hstrict := mul_lt_mul_of_pos_right hdc (show 0 < y k by linarith [hy k])
    change y i + y j < c * y k
    change y i + y j ≤ y k * d at hh
    linarith

/-- Compress to a prescribed label type; unused labels are placed at one. -/
theorem uniform_factorization {C : ℝ} (hC : 1 < C) (hgold : C*C < C+1) :
    ∃ B : ℕ, 0 < B ∧ ∀ (c : ℝ), 1 < c → c ≤ C → ∀ (n : ℕ) (x : Fin n → ℝ),
      Cfg c x → ∃ (z : Fin B → ℝ) (e : Fin n → Fin B), Cfg c z ∧
        ∀ i j k, Win c x i j k → Win c z (e i) (e j) (e k) := by
  classical
  obtain ⟨K, hK⟩ := uniform_compression hC hgold
  refine ⟨K+1, Nat.zero_lt_succ _, ?_⟩
  intro c hc hcC n x hx
  obtain ⟨y, hy, hcard, hwin⟩ := hK c hc hcC x hx
  let S : Finset ℝ := univ.image y
  have hbound : Fintype.card S ≤ K+1 := by
    rw [Fintype.card_coe]
    exact hcard.trans (Nat.le_succ K)
  let emb : S ↪ Fin (K+1) := (Fintype.equivFin S).toEmbedding.trans (Fin.castLEEmb hbound)
  let z : Fin (K+1) → ℝ := Function.extend emb Subtype.val (fun _ => 1)
  let idx (i : Fin n) : S := ⟨y i, mem_image_of_mem y (mem_univ i)⟩
  have hit (p : S) : z (emb p) = (p:ℝ) := emb.injective.extend_apply _ _ p
  refine ⟨z, fun i => emb (idx i), ?_, ?_⟩
  · intro k
    by_cases h : ∃ p, emb p = k
    · obtain ⟨p, rfl⟩ := h
      rw [hit]
      obtain ⟨i, _, hi⟩ := mem_image.mp p.property
      rw [← hi]
      exact hy i
    · have hk : z k = 1 := Function.extend_apply' _ _ k h
      rw [hk]
      exact ⟨le_rfl, hc⟩
  · intro i j k hw
    simpa only [Win, hit] using hwin i j k hw

#print axioms uniform_factorization

#print axioms uniform_compression

end OneScale
