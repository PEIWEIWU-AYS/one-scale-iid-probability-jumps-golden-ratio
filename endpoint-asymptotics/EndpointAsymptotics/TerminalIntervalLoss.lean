import EndpointAsymptotics.TerminalRescaling
import EndpointAsymptotics.BandLossKernel

open Finset OneScale IidJumpSpectra IidInfiniteJumps
open scoped BigOperators
noncomputable section
namespace TerminalRescaling

/-- A lower tail of the population loss controls the cube of the mass in the
terminal interval. The subweights may be a fraction of any endpoint atom. -/
theorem terminal_mass_bound {n : ℕ} (K d : ℕ) {c r z : ℝ} (hr : 1<r) (hc : c<2)
    (hz : 0≤z) (gate : r*(1+(r⁻¹)^d)≤c) (fit : (r⁻¹)^(K+d)≤2-c)
    (x w u : Fin n → ℝ) (hx : ∀ i, 0≤x i) (hw : Mass w) (hu : ∀ i, 0≤u i)
    (uw : ∀ i, u i≤w i) (inside : ∀ i, u i≠0 → (1-(r⁻¹)^K)*z≤x i ∧ x i≤z) :
    (∑ i, u i)^3 ≤ 3*((d:ℝ)+1)*(2/3-score c x w) := by
  let e := 2-(r⁻¹)^d
  let a := (1-(r⁻¹)^K)*z
  have hr0 : 0<r := by linarith
  have hrinv : r⁻¹≤1 := by rw [←one_div];exact (div_le_iff₀ hr0).2 (by linarith)
  have ha : 0≤a := mul_nonneg (sub_nonneg.mpr (pow_le_one₀ (inv_nonneg.mpr hr0.le) hrinv)) hz
  have width : (2-e)*(z-a)≤(2-c)*z := by
    calc
      _ = (r⁻¹)^(K+d)*z := by rw [pow_add];dsimp only [e,a];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right fit hz
  have cap := terminal_score_cap (e:=e) (a:=a) hc.le ha width x u hu inside
  have restrict := BandLossKernel.restricted_loss_le hc.le x w u hx hw hu uw
  obtain ⟨e1,e2,ed⟩ := effective_depth d hr (gate.trans_lt hc)
  change logDepth e≤(d:ℝ) at ed
  have epos : 0<logDepth e := logDepth_pos e1 e2
  have denom : 0<3*((d:ℝ)+1) := by positivity
  have gap : 1/(3*((d:ℝ)+1)) ≤ 2/3-extremal 2 e := by
    apply le_trans _ (inverse_log_bounds e1 e2).1
    apply one_div_le_one_div_of_le (by positivity : 0<3*(logDepth e+1))
    linarith only [ed]
  let q := ∑ i, u i
  have hq : 0≤q := sum_nonneg (fun i _ => hu i)
  change score c x u ≤ q^3 * extremal 2 e at cap
  change 2/3*q^3-score c x u ≤ _ at restrict
  change q^3≤_
  rw [mul_comm (3*((d:ℝ)+1))]
  apply (div_le_iff₀ denom).mp
  have scaled := mul_le_mul_of_nonneg_right gap (pow_nonneg hq 3)
  calc
    q^3/(3*((d:ℝ)+1)) = (1/(3*((d:ℝ)+1)))*q^3 := by ring
    _ ≤ (2/3-extremal 2 e)*q^3 := scaled
    _ ≤ 2/3-score c x w := by nlinarith only [cap,restrict]

#print axioms terminal_mass_bound
end TerminalRescaling
