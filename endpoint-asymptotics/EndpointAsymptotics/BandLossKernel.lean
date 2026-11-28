import EndpointAsymptotics.RankPopulationEndpoint

open Finset OneScale
open scoped BigOperators
noncomputable section
namespace BandLossKernel

def avg3 {n : ℕ} (w : Fin n → ℝ) (f : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, w i*w j*w k*f i j k

def flag (p : Prop) [Decidable p] : ℝ := if p then 1 else 0

def wins (c u v t : ℝ) := flag (u+v<c*t)

def tripleLoss (c u v t : ℝ) : ℝ :=
  2-(wins c u v t+wins c v t u+wins c t u v)

theorem avg3_mono {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0≤w i)
    {f g : Fin n → Fin n → Fin n → ℝ} (h : ∀ i j k, f i j k≤g i j k) : avg3 w f≤avg3 w g := by
  apply sum_le_sum;intro i _;apply sum_le_sum;intro j _;apply sum_le_sum;intro k _
  exact mul_le_mul_of_nonneg_left (h i j k) (mul_nonneg (mul_nonneg (hw i) (hw j)) (hw k))

theorem avg3_add {n : ℕ} (w : Fin n → ℝ) (f g : Fin n → Fin n → Fin n → ℝ) :
    avg3 w (fun i j k => f i j k+g i j k)=avg3 w f+avg3 w g := by
  simp [avg3,mul_add,sum_add_distrib]

theorem avg3_sub {n : ℕ} (w : Fin n → ℝ) (f g : Fin n → Fin n → Fin n → ℝ) :
    avg3 w (fun i j k => f i j k-g i j k)=avg3 w f-avg3 w g := by
  simp [avg3,mul_sub,sum_sub_distrib]

theorem avg3_rotate {n : ℕ} (w : Fin n → ℝ) (f : Fin n → Fin n → Fin n → ℝ) :
    avg3 w (fun i j k => f j k i)=avg3 w f := by
  unfold avg3
  rw [sum_comm]
  apply sum_congr rfl;intro j _
  rw [sum_comm];apply sum_congr rfl;intro k _
  apply sum_congr rfl;intro i _;ring

theorem avg3_product {n : ℕ} (w a b h : Fin n → ℝ) :
    avg3 w (fun i j k => a i*b j*h k) =
      (∑ i, w i*a i)*(∑ j, w j*b j)*(∑ k, w k*h k) := by
  calc
    _ = ∑ i, w i*a i*(∑ j, w j*b j*(∑ k, w k*h k)) := by
      unfold avg3
      simp only [mul_sum]
      apply sum_congr rfl;intro i _;apply sum_congr rfl;intro j _;apply sum_congr rfl;intro k _;ring
    _ = _ := by simp only [←sum_mul];ring

theorem avg3_const {n : ℕ} (w : Fin n → ℝ) (t : ℝ) :
    avg3 w (fun _ _ _ => t)=t*(∑ i, w i)^3 := by
  let a := fun _ : Fin n => t
  let u := fun _ : Fin n => (1:ℝ)
  have h := avg3_product w a u u
  simp only [a,u,mul_one,←sum_mul] at h
  rw [h];ring

theorem avg3_wins {n : ℕ} (w x : Fin n → ℝ) (c : ℝ) :
    avg3 w (fun i j k => wins c (x i) (x j) (x k))=score c x w := by
  unfold avg3 score
  apply sum_congr rfl;intro i _;apply sum_congr rfl;intro j _;apply sum_congr rfl;intro k _
  by_cases h : x i+x j<c*x k <;> simp [OneScale.Win,wins,flag,h]

theorem avg3_loss {n : ℕ} (w x : Fin n → ℝ) (c : ℝ) :
    avg3 w (fun i j k => tripleLoss c (x i) (x j) (x k)) =
      2*(∑ i, w i)^3-3*score c x w := by
  let f := fun i j k => wins c (x i) (x j) (x k)
  change avg3 w (fun i j k => 2-(f i j k+f j k i+f k i j))=_
  rw [avg3_sub,avg3_add,avg3_add,avg3_const,avg3_rotate,
    avg3_rotate w (fun a b d => f b d a),avg3_rotate]
  dsimp only [f]; rw [avg3_wins];ring

theorem tripleLoss_nonneg {c u v t : ℝ} (hc : c≤2) (hu : 0≤u) (hv : 0≤v) (ht : 0≤t) :
    0≤tripleLoss c u v t := by
  have h1 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc) hu
  have h2 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc) hv
  have h3 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc) ht
  unfold tripleLoss wins flag
  split_ifs <;> norm_num; linarith

/-- The loss on triples entirely within any subprobability of a finite law
is bounded by the full population loss. -/
theorem restricted_loss_le {n : ℕ} {c : ℝ} (hc : c≤2) (x w u : Fin n → ℝ)
    (hx : ∀ i, 0≤x i) (hw : Mass w) (hu : ∀ i, 0≤u i) (uw : ∀ i, u i≤w i) :
    (2/3:ℝ)*(∑ i, u i)^3 - score c x u ≤ 2/3-score c x w := by
  have h : avg3 u (fun i j k => tripleLoss c (x i) (x j) (x k)) ≤
      avg3 w (fun i j k => tripleLoss c (x i) (x j) (x k)) := by
    apply sum_le_sum;intro i _;apply sum_le_sum;intro j _;apply sum_le_sum;intro k _
    apply mul_le_mul_of_nonneg_right _ (tripleLoss_nonneg hc (hx i) (hx j) (hx k))
    exact mul_le_mul (mul_le_mul (uw i) (uw j) (hu j) (hw.1 i)) (uw k) (hu k) (mul_nonneg (hw.1 i) (hw.1 j))
  rw [avg3_loss,avg3_loss,hw.2,one_pow] at h
  linarith only [h]

#print axioms restricted_loss_le
end BandLossKernel
