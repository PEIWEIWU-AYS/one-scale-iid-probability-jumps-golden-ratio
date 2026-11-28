import EndpointAsymptotics.RankPopulationEndpoint

open EndpointRecursion Filter
open scoped Topology
noncomputable section
namespace FullRankWindow

private theorem reciprocal_step_bounds (n : ℕ) :
    1/2 ≤ (x (n+1))⁻¹-(x n)⁻¹ ∧ (x (n+1))⁻¹-(x n)⁻¹ ≤ 1 := by
  have h := reciprocal_step n
  let s := Real.sqrt (1+x n)
  change (x (n+1))⁻¹-(x n)⁻¹=(s+2)/(2*(s+1)) at h
  have hs : 0≤s := Real.sqrt_nonneg _
  have pos : 0<2*(s+1) := by linarith
  rw [h]
  constructor
  · apply (le_div_iff₀ pos).2; linarith
  · apply (div_le_iff₀ pos).2; linarith

private theorem recip_span (n k : ℕ) :
    (k:ℝ)/2 ≤ (x (n+k))⁻¹-(x n)⁻¹ ∧ (x (n+k))⁻¹-(x n)⁻¹ ≤ (k:ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨lo,hi⟩ := reciprocal_step_bounds (n+k)
    push_cast
    rw [← Nat.add_assoc]
    constructor <;> linarith only [ih.1,ih.2,lo,hi]

private theorem x_span (n k : ℕ) : x (n+k)≤x n ∧
    x n-x (n+k)≤(k:ℝ)*(x n)^2 := by
  obtain ⟨lo,hi⟩ := recip_span n k
  have hp := xpos (n+k)
  have hq := xpos n
  have down : x (n+k)≤x n := (inv_le_inv₀ hq hp).1 (by linarith [Nat.cast_nonneg (α:=ℝ) k])
  refine ⟨down,?_⟩
  have h := mul_le_mul_of_nonneg_right hi (mul_pos hp hq).le
  have id : ((x (n+k))⁻¹-(x n)⁻¹)*(x (n+k)*x n)=x n-x (n+k) := by
    field_simp [hp.ne',hq.ne']
  rw [id] at h
  exact h.trans <| by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [sq]
    exact mul_le_mul_of_nonneg_right down hq.le

private theorem eventually_small_x : ∀ᶠ n : ℕ in atTop, x n≤1/2 := by
  filter_upwards [eventually_ge_atTop 4] with n hn
  have h := (recip_span 0 n).1
  simp only [Nat.zero_add, x] at h
  have nc : (4:ℝ)≤n := by exact_mod_cast hn
  have hp := xpos n
  have inv : 2 ≤ (x n)⁻¹ := by linarith
  have ht := mul_le_mul_of_nonneg_right inv hp.le
  rw [inv_mul_cancel₀ hp.ne'] at ht
  linarith

private theorem ceiling_extra (j : ℕ) (small : x j≤1/2) (r : ℝ) (hr : 0≤r) :
    (peak j+2*r+r^2)/(1+3*r+3*r^2) ≤ peak j+(x j)^2 := by
  have p := optimal_deficit j
  have coef : 1/2≤3*peak j-1 := by linarith
  have pen := mul_le_mul_of_nonneg_right coef (sq_nonneg r)
  have h : 2*r+r^2-(3*r+3*r^2)*peak j≤(x j)^2 := by
    have lin := congrArg (fun t : ℝ => 3*t*r) p
    dsimp at lin
    nlinarith only [lin,pen,sq_nonneg (x j-r),sq_nonneg (x j)]
  apply (div_le_iff₀ (by nlinarith only [hr,sq_nonneg r] : 0<1+3*r+3*r^2)).2
  nlinarith only [h,mul_nonneg (sq_nonneg (x j)) (show 0≤3*r+3*r^2 by nlinarith only [hr,sq_nonneg r])]

/-- The bound is valid simultaneously for every number of removed levels. -/
theorem rank_ceiling_cost_uniform :
    ∀ᶠ n : ℕ in atTop, ∀ (k : ℕ) (r : ℝ), 0≤r →
      (peak (n+k)+2*r+r^2)/(1+3*r+3*r^2) ≤ peak n+(1+(k:ℝ)/3)*(x n)^2 := by
  filter_upwards [eventually_small_x] with n small
  intro k r hr
  obtain ⟨down,h⟩ := x_span n k
  have cheap := ceiling_extra (n+k) (down.trans small) r hr
  have square := pow_le_pow_left₀ (xpos (n+k)).le down 2
  linarith only [cheap,square,h,optimal_deficit n,optimal_deficit (n+k)]

/-- Removing a fixed number of outer levels and optimizing the lower-layer
odds together cost at most a constant times the squared optimal deficit. -/
theorem rank_ceiling_cost (k : ℕ) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ r : ℝ, 0≤r →
      (peak (n+k)+2*r+r^2)/(1+3*r+3*r^2) ≤ peak n+C*(x n)^2 :=
  ⟨1+(k:ℝ)/3,rank_ceiling_cost_uniform.mono (fun _ h => h k)⟩

#print axioms rank_ceiling_cost_uniform
#print axioms rank_ceiling_cost
end FullRankWindow
