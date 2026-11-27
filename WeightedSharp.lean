import WeightedBridge

open Finset Set Filter
open scoped BigOperators Topology
noncomputable section
namespace OneScale.WeightedSharp
open OneScale.WeightedBridge

theorem beta_four_thirds : beta (4/3 : ℝ) = 0 := by
  have all_zero (b : ℝ) (hb : b ∈ values (4/3)) : b=0 := by
    obtain ⟨n,x,w,hcfg,_,rfl⟩ := hb
    have impossible (i j k : Fin n) : ¬Win (4/3) x i j k := by
      dsimp [Win]
      linarith [(hcfg i).1,(hcfg j).1,(hcfg k).2]
    simp [score,impossible]
  have hn := values_nonempty (show (1:ℝ)<4/3 by norm_num)
  obtain ⟨b,hb⟩ := hn
  apply le_antisymm (csSup_le ⟨b,hb⟩ (fun y hy => (all_zero y hy).le))
  simpa only [all_zero b hb] using le_csSup (bdd_values (4/3)) hb

def points : Fin 2 → ℝ := ![1,4]
def weights (p : ℝ) : Fin 2 → ℝ := ![p,1-p]

theorem two_atom_mass {p : ℝ} (hp : p ∈ Set.Icc 0 1) : Mass (weights p) := by
  constructor
  · intro i; fin_cases i <;> simp [weights,hp.1,hp.2]
  · simp [weights,Fin.sum_univ_two]

theorem two_atom_spread (p : ℝ) : spread (4/3) points (weights p) = p*(1-p) := by
  change (∑ i,∑ j,weights p i*weights p j *
    (if (4/3:ℝ)*points i≤points j then 1 else 0)) = _
  norm_num [Fin.sum_univ_two,points,weights]

theorem two_atom_score (p : ℝ) :
    score (4/3) points (weights p) = (2-p)*spread (4/3) points (weights p) := by
  rw [two_atom_spread]
  norm_num [score,Win,Fin.sum_univ_two,points,weights]
  ring

/-- The exact surplus of the compression upper bound on the two-point family. -/
theorem two_atom_gap (p : ℝ) :
    beta (4/3) + (2*spread (4/3) points (weights p) - (spread (4/3) points (weights p))^2)
      - score (4/3) points (weights p) = p^2 * spread (4/3) points (weights p) := by
  rw [beta_four_thirds,two_atom_score,two_atom_spread]; ring

/-- Every uniform correction A*D-B*D² requires A≥2. At A=2 it requires B≤1.
It suffices to test only positive two-point laws at the fixed coefficient 4/3. -/
theorem coefficients_necessary {A B : ℝ} (h : ∀ p ∈ Ioo (0:ℝ) 1,
    score (4/3) points (weights p) ≤ beta (4/3) +
      A*spread (4/3) points (weights p) - B*(spread (4/3) points (weights p))^2) :
    2 ≤ A ∧ (A=2 → B≤1) := by
  have small : ∀ᶠ p : ℝ in 𝓝[>] 0, p ∈ Ioo (0:ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ)),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with p hl hu
    exact ⟨hl,hu⟩
  have ev : ∀ᶠ p : ℝ in 𝓝[>] 0, 2-p ≤ A-B*(p*(1-p)) := by
    filter_upwards [small] with p hp
    have hh := h p hp
    rw [beta_four_thirds,two_atom_score,two_atom_spread] at hh
    have hd := mul_pos hp.1 (sub_pos.mpr hp.2)
    apply (le_of_mul_le_mul_right ?_ hd : 2-p ≤ A-B*(p*(1-p)))
    nlinarith only [hh]
  have het : Tendsto (fun p : ℝ => p) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  constructor
  · have hlim := le_of_tendsto_of_tendsto
      ((tendsto_const_nhds (x:=(2:ℝ))).sub het)
      ((tendsto_const_nhds (x:=A)).sub ((tendsto_const_nhds (x:=B)).mul
        (het.mul ((tendsto_const_nhds (x:=(1:ℝ))).sub het)))) ev
    simpa using hlim
  · rintro rfl
    have ev' : ∀ᶠ p : ℝ in 𝓝[>] 0, B*(1-p)≤1 := by
      filter_upwards [small,ev] with p hp hsmall
      apply (le_of_mul_le_mul_right ?_ hp.1 : B*(1-p)≤1)
      nlinarith only [hsmall]
    have hlim := le_of_tendsto_of_tendsto
      ((tendsto_const_nhds (x:=B)).mul ((tendsto_const_nhds (x:=(1:ℝ))).sub het))
      (tendsto_const_nhds (x:=(1:ℝ))) ev'
    simpa using hlim

#print axioms coefficients_necessary
end OneScale.WeightedSharp
