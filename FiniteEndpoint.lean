import FiniteProfile
import Endpoint

open IidJumpSpectra Filter Set
open scoped Topology

namespace IidStaircase

/-- Each fixed left neighbourhood of 2 eventually contains at least K genuine
right jumps of the exact N-label optimum, for every fixed K. -/
theorem many_finite_jumps_before_two (a : ℝ) (ha : a < 2) (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∃ b : Fin K ↪ ℝ, ∀ i,
      b i ∈ Set.Ioo a 2 ∧ RightJump (finiteProfile 2 N) (b i) (1/(N:ℝ)^3) ∧
        ¬ ContinuousAt (finiteProfile 2 N) (b i) := by
  classical
  let below := Set.Iio (2 : ℝ)
  have hs (x : below) : ∃ y : below, x.val < y.val ∧ extremal 2 x.val < extremal 2 y.val := by
    obtain ⟨y, hxy, hy2, hy⟩ := IidInfiniteJumps.larger_before_two (a := x.val) x.property
    exact ⟨⟨y,hy2⟩,hxy,hy⟩
  choose step hstrict hincrease using hs
  let r : ℕ → below := Nat.rec ⟨(a+2)/2, by change (a+2)/2 < 2; linarith⟩ (fun _ x => step x)
  have hstep (n : ℕ) : r (n+1) = step (r n) := rfl
  have hmono : StrictMono (fun n => (r n).val) := strictMono_nat_of_lt_succ fun n => by
    rw [hstep]
    exact hstrict _
  have hab (n : ℕ) : a < (r n).val := by
    have hz : a < (r 0).val := by change a < (a+2)/2; linarith
    exact hz.trans_le (hmono.monotone (Nat.zero_le n))
  let s (i : Fin K) := (r i.val).val
  let t (i : Fin K) := (r (i.val+1)).val
  have hg (i : Fin K) : extremal 2 (s i) < extremal 2 (t i) := hincrease (r i.val)
  have hd (i j : Fin K) (hne : i ≠ j) : Disjoint (Set.Ico (s i) (t i)) (Set.Ico (s j) (t j)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hsep : t i ≤ s j := hmono.monotone (show i.val+1 ≤ j.val from hij)
      exact (not_lt_of_ge (hsep.trans hy.1)) hx.2
    · have hsep : t j ≤ s i := hmono.monotone (show j.val+1 ≤ i.val from hji)
      exact (not_lt_of_ge (hsep.trans hx.1)) hy.2
  filter_upwards [eventually_many_finiteProfile_jumps s t hg hd] with N hN
  obtain ⟨b,hb⟩ := hN
  refine ⟨b, fun i => ?_⟩
  obtain ⟨hi,hj,hc⟩ := hb i
  exact ⟨⟨(hab _).trans_le hi.1, hi.2.trans (r (i.val+1)).property⟩, hj, hc⟩

#print axioms many_finite_jumps_before_two
end IidStaircase
