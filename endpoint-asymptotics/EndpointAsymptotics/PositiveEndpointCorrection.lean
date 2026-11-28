import EndpointAsymptotics.MultinacciWitnessBarrier

open Finset EndpointRecursion IidJumpSpectra Filter
open scoped BigOperators Topology
noncomputable section
namespace FullRankWindow

private theorem reciprocal_step_error (n : ℕ) :
    3/4-x n/16 ≤ (x (n+1))⁻¹-(x n)⁻¹ ∧ (x (n+1))⁻¹-(x n)⁻¹≤3/4 := by
  let s := Real.sqrt (1+x n)
  have hs := Real.sq_sqrt (show 0≤1+x n by linarith [xpos n])
  change s^2=1+x n at hs
  have pos : 0≤s := Real.sqrt_nonneg _
  have h1 : 1≤s := by nlinarith only [hs,pos,xpos n]
  have dpos : 0<4*(1+s)^2 := by positivity
  have eq := reciprocal_step n
  change (x (n+1))⁻¹-(x n)⁻¹=(s+2)/(2*(s+1)) at eq
  have ref : (s+2)/(2*(s+1))=3/4-x n/(4*(1+s)^2) := by
    rw [show x n=s^2-1 by linarith only [hs]]
    field_simp [show 1+s≠0 by linarith,show s+1≠0 by linarith];ring
  rw [eq,ref]
  have bd : x n/(4*(1+s)^2)≤x n/16 := by
    apply div_le_div_of_nonneg_left (xpos n).le (by norm_num)
    nlinarith only [h1,sq_nonneg (s-1)]
  constructor
  · linarith only [bd]
  · linarith only [div_nonneg (xpos n).le dpos.le]

private theorem reciprocal_enclosure (n : ℕ) :
    1/2+3*(n:ℝ)/4-(∑ j ∈ range n,x j)/16≤(x n)⁻¹ ∧ (x n)⁻¹≤1/2+3*(n:ℝ)/4 := by
  induction n with
  | zero => norm_num [x]
  | succ n ih =>
    obtain ⟨lo,hi⟩ := reciprocal_step_error n
    rw [sum_range_succ,Nat.cast_succ]
    constructor <;> linarith only [lo,hi,ih.1,ih.2]

private theorem deficit_comparison (n : ℕ) :
    4/(3*((n:ℝ)+5))≤x n ∧ x n-4/(3*((n:ℝ)+5))≤
      (x n)^2*(4+(∑ j ∈ range (n+1),x j)/16) := by
  let A := 3*((n:ℝ)+5)/4
  have pa : 0<A := by dsimp [A];positivity
  have px := xpos n
  let U := ∑ j ∈ range (n+1), x j
  have nn : 0≤U := sum_nonneg (fun i _ => (xpos i).le)
  obtain ⟨lo,hi⟩ := reciprocal_enclosure n
  have bound : A-(x n)⁻¹ ≤ 4+U/16 := by
    dsimp only [A,U];rw [sum_range_succ];linarith only [lo,px]
  have less : (x n)⁻¹ ≤ A := by dsimp [A];linarith only [hi]
  have inv : A⁻¹≤x n := by simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr px) less
  have mul := mul_le_mul_of_nonneg_left bound (mul_nonneg px.le (inv_nonneg.mpr pa.le))
  have step : x n - A⁻¹=x n*A⁻¹*(A-(x n)⁻¹) := by field_simp [pa.ne',px.ne'];ring
  have sl : x n*A⁻¹ ≤ (x n)^2 := by simpa only [pow_two] using mul_le_mul_of_nonneg_left inv px.le
  have out := (step.le.trans mul).trans (mul_le_mul_of_nonneg_right sl (by linarith only [nn]))
  have replace : 4/(3*((n:ℝ)+5))=A⁻¹ := by dsimp [A];rw [inv_div]
  rw [replace];exact ⟨inv,out⟩

/-- For all sufficiently large multinacci indices the strict unrestricted
population exceeds its first-order approximation by an explicit positive
multiple of log(m-3)/m^2, where m=n+5. -/
theorem positive_logarithmic_population_correction :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℝ, 1<c → c<2 → (2-c)*c^(n+5)=1 →
      2/3-4/(9*((n:ℝ)+5)) + Real.log ((n:ℝ)+2)/(1000*((n:ℝ)+5)^2) ≤ extremal 2 c := by
  obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp 100)
  filter_upwards [eventually_ge_atTop N] with n num
  intro c hc h2 root
  obtain ⟨w,hw,hs,hm⟩ := optimal_cube_mass n
  have split := split_rank_lower (threshold_near_two hc root) h2 root w hw
  rw [hs] at split
  let U := ∑ j ∈ range (n+1), x j
  let z := Real.log ((n:ℝ)+2)
  let m := (n:ℝ)+5
  have pp : 0<m := by dsimp [m];positivity
  have logb := log_le_sum_deficit (n+1)
  push_cast at logb
  have lsum : z≤U := by simpa only [z,U,show (n:ℝ)+1+1=n+2 by ring] using logb
  have lbig : 100<z := by
    dsimp only [z];rw [←Real.log_exp 100]
    have nge : (N:ℝ)≤n := by exact_mod_cast num
    exact Real.log_lt_log (Real.exp_pos _) (by linarith only [hN,nge])
  obtain ⟨lo,err⟩ := deficit_comparison n
  change 4/(3*m)≤x n at lo
  change x n-4/(3*m) ≤ (x n)^2*(4+U/16) at err
  change (x n)^2/8*U≤_ at hm
  have poly : 2/3-4/(9*m)+(x n)^2*(5/192*U-4/3) ≤ extremal 2 c := by
    have shift : 4/(3*m)=3*(4/(9*m)) := by ring
    linarith only [split,hm,optimal_deficit n,err,shift]
  have coeff : z/1000 ≤ 5/192*U-4/3 := by linarith only [lsum,lbig]
  have kk := mul_le_mul_of_nonneg_left coeff (sq_nonneg (x n))
  have weaker : 1/m≤4/(3*m) := by
    apply (div_le_div_iff₀ pp (by positivity)).2
    linarith only [pp]
  have zz : 1/m≤x n := weaker.trans lo
  have sq := pow_le_pow_left₀ (one_div_nonneg.mpr pp.le) zz 2
  have k := mul_le_mul_of_nonneg_right sq (show 0≤z/1000 by linarith)
  have id : (1/m)^2*(z/1000)=z/(1000*m^2) := by ring
  change 2/3-4/(9*m)+z/(1000*m^2) ≤ _
  linarith only [k,kk,poly,id]

#print axioms positive_logarithmic_population_correction
end FullRankWindow
