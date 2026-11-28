import Mathlib.Tactic

open Filter
open scoped Topology
noncomputable section
namespace FullRankWindow

/-- A normalized block with n+1 labels numbered in descending order;
the predicate prescribes every ordered pair and every ordered triple. -/
def Realizes (rel : ℝ → ℝ → Prop) (n : ℕ) (c : ℝ) : Prop :=
  ∃ x : ℕ → ℝ, x 0=1 ∧ (∀ i ≤ n, 0 < x i) ∧
    (∀ i ≤ n, ∀ k ≤ n, rel (x i) (c*x k)) ∧
    (∀ i ≤ n, ∀ j ≤ n, ∀ k ≤ n, rel (x i+x j) (c*x k) ↔ k < i ∨ k < j)

private def level (c : ℝ) (j : ℕ) := (1-(2-c)*c^j)/(c-1)

private theorem level_zero {c : ℝ} (hc : 1 < c) : level c 0=1 := by
  dsimp [level]
  field_simp [show c-1 ≠ 0 by linarith]
  ring

private theorem step {c : ℝ} (hc : 1 < c) (j : ℕ) : 1+level c (j+1)=c*level c j := by
  dsimp [level]
  rw [pow_succ]
  field_simp [show c-1 ≠ 0 by linarith]
  ring

private theorem down {c : ℝ} (hc : 1 < c) (h2 : c < 2) : Antitone (level c) := by
  apply antitone_nat_of_succ_le
  intro i
  dsimp [level]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have hp := pow_le_pow_right₀ hc.le (show i ≤ i+1 by omega)
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hp (by linarith)) 1

private theorem bottom_iff {c : ℝ} (hc : 1 < c) (n : ℕ) :
    1 ≤ c*level c n ↔ (2-c)*c^(n+1) ≤ 1 := by
  simp only [level,pow_succ,←mul_div_assoc]
  rw [le_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith only [h]

private theorem bottom_strict_iff {c : ℝ} (hc : 1 < c) (n : ℕ) :
    1 < c*level c n ↔ (2-c)*c^(n+1) < 1 := by
  simp only [level,pow_succ,←mul_div_assoc]
  rw [lt_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith only [h]

private theorem upper_of_steps {c : ℝ} (hc : 1 < c) {n : ℕ} {x : ℕ → ℝ} (hx : x 0=1)
    (h : ∀ j < n, 1+x (j+1) ≤ c*x j) : ∀ j ≤ n, x j ≤ level c j := by
  intro j
  induction j with
  | zero => intro _; rw [hx,level_zero hc]
  | succ j ih =>
    intro hj
    have bound := mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith : 0 ≤ c)
    linarith only [h j (by omega),bound,step hc j]

/-- The maximally winning finite pattern is weakly realizable exactly at and
above the n+1-level multinacci threshold. -/
theorem weak_iff {n : ℕ} {c : ℝ} (hc : 1 < c) (h2 : c < 2) :
    Realizes (· ≤ ·) n c ↔ (2-c)*c^(n+1) ≤ 1 := by
  have hc0 : 0 < c := by linarith
  constructor
  · rintro ⟨x,hx,_,pairs,win⟩
    have st (j : ℕ) (hj : j < n) : 1+x (j+1) ≤ c*x j := by
      rw [←hx]
      exact (win 0 (by omega) (j+1) (by omega) j (by omega)).2 (Or.inr (by omega))
    have bot := pairs 0 (by omega) n le_rfl
    rw [hx] at bot
    exact (bottom_iff hc n).1 (bot.trans (mul_le_mul_of_nonneg_left
      (upper_of_steps hc hx st n le_rfl) hc0.le))
  · intro h
    have bot := (bottom_iff hc n).2 h
    have pos (i : ℕ) (hi : i ≤ n) : 0 < level c i := by
      have bn : 0 < level c n := pos_of_mul_pos_right (by linarith : 0 < c*level c n) hc0.le
      exact bn.trans_le (down hc h2 hi)
    have top (i : ℕ) : level c i ≤ 1 := level_zero hc ▸ down hc h2 (Nat.zero_le i)
    refine ⟨level c,level_zero hc,pos,fun i _ k hk => (top i).trans (bot.trans
      (mul_le_mul_of_nonneg_left (down hc h2 hk) hc0.le)),?_⟩
    intro i _ j _ k hk
    constructor
    · contrapose!
      rintro ⟨hi,hj⟩
      linarith only [down hc h2 hi,down hc h2 hj,mul_pos (sub_pos.mpr h2) (pos k hk)]
    · rintro (hi | hj)
      · linarith only [down hc h2 (show k+1 ≤ i from hi),top j,step hc k]
      · linarith only [down hc h2 (show k+1 ≤ j from hj),top i,step hc k]

/-- The strict version excludes the threshold itself. -/
theorem strict_iff {n : ℕ} {c : ℝ} (hc : 1 < c) (h2 : c < 2) :
    Realizes (· < ·) n c ↔ (2-c)*c^(n+1) < 1 := by
  have hc0 : 0 < c := by linarith
  constructor
  · rintro ⟨x,hx,_,pairs,win⟩
    have st (j : ℕ) (hj : j < n) : 1+x (j+1) ≤ c*x j := by
      rw [←hx]
      exact ((win 0 (by omega) (j+1) (by omega) j (by omega)).2 (Or.inr (by omega))).le
    have bot := pairs 0 (by omega) n le_rfl
    rw [hx] at bot
    exact (bottom_strict_iff hc n).1 (bot.trans_le (mul_le_mul_of_nonneg_left
      (upper_of_steps hc hx st n le_rfl) hc0.le))
  · intro h
    have hh : ContinuousAt (fun d : ℝ => (2-d)*d^(n+1)) c := by fun_prop
    have good : ∀ᶠ d in 𝓝[<] c, (2-d)*d^(n+1) < 1 :=
      (hh.tendsto.eventually_lt_const h).filter_mono nhdsWithin_le_nhds
    have gt : ∀ᶠ d in 𝓝[<] c, 1 < d := (eventually_gt_nhds hc).filter_mono nhdsWithin_le_nhds
    have lt : ∀ᶠ d in 𝓝[<] c, d < c := self_mem_nhdsWithin
    obtain ⟨d,hd,hdc,hgood⟩ := (gt.and (lt.and good)).exists
    have hd2 := hdc.trans h2
    have bot := (bottom_iff hd n).2 hgood.le
    have pos (i : ℕ) (hi : i ≤ n) : 0 < level d i := by
      have bn : 0 < level d n := pos_of_mul_pos_right (by linarith : 0 < d*level d n) (by linarith)
      exact bn.trans_le (down hd hd2 hi)
    have top (i : ℕ) : level d i ≤ 1 := level_zero hd ▸ down hd hd2 (Nat.zero_le i)
    refine ⟨level d,level_zero hd,pos,?_,?_⟩
    · intro i _ k hk
      exact ((top i).trans (bot.trans (mul_le_mul_of_nonneg_left (down hd hd2 hk)
        (by linarith)))).trans_lt (mul_lt_mul_of_pos_right hdc (pos k hk))
    · intro i _ j _ k hk
      constructor
      · contrapose!
        rintro ⟨hi,hj⟩
        linarith only [down hd hd2 hi,down hd hd2 hj,mul_pos (sub_pos.mpr h2) (pos k hk)]
      · intro hwin
        apply lt_of_le_of_lt _ (mul_lt_mul_of_pos_right hdc (pos k hk))
        rcases hwin with hi | hj
        · linarith only [down hd hd2 (show k+1 ≤ i from hi),top j,step hd k]
        · linarith only [down hd hd2 (show k+1 ≤ j from hj),top i,step hd k]

#print axioms weak_iff
#print axioms strict_iff
end FullRankWindow
