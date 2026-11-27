import OneScaleCompression

namespace OneScale

/-- The limiting positions of the ordinary and branching ladders. -/
noncomputable def ladderValue (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => (1+ladderValue c n)/c

noncomputable def branchValue (c : ℝ) : ℕ → ℝ
  | 0 => 4/c^2
  | n+1 => (1+branchValue c n)/c

def LadderCandidate (c : ℝ) : Prop :=
  (∃ n : ℕ, ladderValue c n = c) ∨ ∃ n : ℕ, branchValue c n = c

namespace ThresholdTree

private lemma two_le_node {c : ℝ} (hc : 0<c) (hc2 : c≤2) (u v : ThresholdTree) :
    2/c ≤ (node u v).value c := by
  dsimp [value]
  apply div_le_div_of_nonneg_right _ hc.le
  linarith [one_le_value hc hc2 u,one_le_value hc hc2 v]

private lemma fork_dichotomy {c : ℝ} (hc : 0<c) (hc2 : c≤2) (u v : ThresholdTree) :
    (node u v).value c = 2/c ∨ (1+2/c)/c ≤ (node u v).value c := by
  cases u with
  | leaf =>
    cases v with
    | leaf => left; simp [value]; ring
    | node a b =>
      right
      exact div_le_div_of_nonneg_right (add_le_add_left (two_le_node hc hc2 a b) 1) hc.le
  | node a b =>
    right
    apply div_le_div_of_nonneg_right _ hc.le
    linarith [two_le_node hc hc2 a b,one_le_value hc hc2 v]

private lemma fork_gap {c : ℝ} (h1 : 1<c) (hg : c*c<c+1) :
    c*c < 2/c+(1+2/c)/c := by
  have hc : 0<c := by linarith
  have hp : 0<c*c+c+2 := by positivity
  have h4 : c^4<3*c+2 := by nlinarith [mul_neg_of_neg_of_pos (sub_neg.mpr hg) hp]
  have ht : (2/c+(1+2/c)/c)*(c*c) = 3*c+2 := by field_simp; ring
  by_contra! h
  have hh := mul_le_mul_of_nonneg_right h (mul_nonneg hc.le hc.le)
  nlinarith

/-- Below the golden ratio every feasible binary recipe is an ordinary ladder
or a single double fork followed by a ladder. -/
theorem feasible_value {c : ℝ} (h1 : 1<c) (hg : c*c<c+1) (t : ThresholdTree)
    (ht : t.value c ≤ c) :
    (∃ n : ℕ, t.value c = ladderValue c n) ∨ ∃ n : ℕ, t.value c = branchValue c n := by
  have hc : 0<c := by linarith
  have hc2 : c≤2 := by nlinarith [sq_nonneg (c-1)]
  induction t with
  | leaf => exact Or.inl ⟨0,rfl⟩
  | node u v iu iv =>
    have hsum : u.value c+v.value c ≤ c*c := (div_le_iff₀ hc).mp ht
    have hu : u.value c ≤ c := by linarith [one_le_value hc hc2 v]
    have hv : v.value c ≤ c := by linarith [one_le_value hc hc2 u]
    specialize iu hu
    specialize iv hv
    cases u with
    | leaf =>
      rcases iv with ⟨n,hn⟩|⟨n,hn⟩
      · exact Or.inl ⟨n+1,by simp [value,ladderValue,hn]⟩
      · exact Or.inr ⟨n+1,by simp [value,branchValue,hn]⟩
    | node a b =>
      cases v with
      | leaf =>
        rcases iu with ⟨n,hn⟩|⟨n,hn⟩
        · exact Or.inl ⟨n+1,by change ((node a b).value c+1)/c=(1+ladderValue c n)/c; rw [hn,add_comm]⟩
        · exact Or.inr ⟨n+1,by change ((node a b).value c+1)/c=(1+branchValue c n)/c; rw [hn,add_comm]⟩
      | node e f =>
        have hgap := fork_gap h1 hg
        have heq (s t p q : ThresholdTree)
            (hbound : (node s t).value c + (node p q).value c ≤ c*c) :
            (node s t).value c = 2/c := by
          rcases fork_dichotomy hc hc2 s t with h|h
          · exact h
          · linarith [two_le_node hc hc2 p q]
        have hleft := heq a b e f hsum
        have hright := heq e f a b (by linarith)
        right
        refine ⟨0,?_⟩
        change ((node a b).value c + (node e f).value c)/c = 4/c^2
        rw [hleft,hright]
        ring

/-- Possible threshold values of binary comparison trees have only two origins. -/
theorem candidate_of_tree_root {c : ℝ} (h1 : 1<c) (hg : c*c<c+1)
    (t : ThresholdTree) (ht : t.value c=c) : LadderCandidate c := by
  rcases feasible_value h1 hg t ht.le with ⟨n,hn⟩|⟨n,hn⟩
  · exact Or.inl ⟨n,hn.symm.trans ht⟩
  · exact Or.inr ⟨n,hn.symm.trans ht⟩

theorem value_continuousAt {c : ℝ} (hc : c≠0) (t : ThresholdTree) :
    ContinuousAt (fun s => t.value s) c := by
  induction t with
  | leaf => exact continuousAt_const
  | node u v hu hv => exact (hu.add hv).div continuousAt_id hc

end ThresholdTree
end OneScale
