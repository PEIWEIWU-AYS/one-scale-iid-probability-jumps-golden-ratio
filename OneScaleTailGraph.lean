import OneScaleMenu
import Mathlib.Topology.Order.Basic

open Filter Set Finset
open scoped Topology
set_option maxHeartbeats 2000000
namespace OneScale.Tail

/-- Masses of the least atom, the first ladder atom, the unbonused labels
and the labels winning against two copies of the first ladder atom. -/
structure Masses where
  p : ℝ
  u : ℝ
  v : ℝ
  h : ℝ

def Valid (k : ℕ) (m : Masses) : Prop :=
  0 ≤ m.p ∧ 0 ≤ m.u ∧ 0 ≤ m.v ∧ 0 ≤ m.h ∧ m.p + m.u + m.v + m.h = 1 ∧
  (k = 0 → m.h = 0)

noncomputable def score (l k : ℕ) (m : Masses) : ℝ :=
  m.p*(1-m.p) - m.p*(m.u^2 + m.v^2/(l:ℝ) + m.h^2/(k:ℝ)) + m.u^2*m.h

def IsMax (l k : ℕ) (m : Masses) : Prop :=
  Valid k m ∧ ∀ y, Valid k y → score l k y ≤ score l k m

private noncomputable def mix (m d : Masses) (t : ℝ) : Masses :=
  ⟨m.p+t*d.p,m.u+t*d.u,m.v+t*d.v,m.h+t*d.h⟩

private noncomputable def grad (l k : ℕ) (m : Masses) : Masses :=
  ⟨1-2*m.p-m.u^2-m.v^2/(l:ℝ)-m.h^2/(k:ℝ), 2*m.u*(m.h-m.p),
    -2*m.p*m.v/(l:ℝ), m.u^2-2*m.p*m.h/(k:ℝ)⟩

private def dot (a b : Masses) : ℝ := a.p*b.p+a.u*b.u+a.v*b.v+a.h*b.h

/-- A feasible one-sided displacement of mass at a maximizer has nonpositive
linear term. The remaining terms are a polynomial in the displacement. -/
private lemma first_order {l k : ℕ} {m : Masses} (hm : IsMax l k m)
    (d : Masses) {a : ℝ} (ha : 0 < a) (hf : ∀ t, 0 ≤ t → t ≤ a → Valid k (mix m d t)) :
    dot (grad l k m) d ≤ 0 := by
  let A := (l:ℝ)⁻¹
  let B := (k:ℝ)⁻¹
  let q := -d.p^2 - m.p*(d.u^2+A*d.v^2+B*d.h^2) -
    2*d.p*(m.u*d.u+A*m.v*d.v+B*m.h*d.h) + d.u^2*m.h+2*m.u*d.u*d.h
  let r := -d.p*(d.u^2+A*d.v^2+B*d.h^2)+d.u^2*d.h
  let g := dot (grad l k m) d
  have expan (t : ℝ) : score l k (mix m d t)-score l k m = t*(g+t*(q+t*r)) := by
    dsimp [g,grad,dot,score,mix,q,r,A,B]
    ring
  have lim : Tendsto (fun t : ℝ => g+t*(q+t*r)) (𝓝[>] 0) (𝓝 g) := by
    have w : ContinuousAt (fun t : ℝ => g+t*(q+t*r)) 0 := by fun_prop
    simpa using w.continuousWithinAt.tendsto (s := Ioi 0)
  apply le_of_tendsto lim
  have ev : ∀ᶠ t : ℝ in 𝓝[>] 0, t < a := (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds
  filter_upwards [ev, self_mem_nhdsWithin (s := Ioi (0:ℝ))] with t ht hp
  have hw := hm.2 (mix m d t) (hf t hp.le ht.le)
  have hw' : t*(g+t*(q+t*r)) ≤ 0 := by linarith [expan t]
  exact nonpos_of_mul_nonpos_right hw' hp

private lemma scalar_low (z u : ℝ) (hz : (1:ℝ)/2 ≤ z) (hz' : z ≤ 1) (hu : 0≤u) :
    (1-z^2)/4 + u^2*(z-u) ≤ 89/432 := by
  have hmax : u^2*(z-u) ≤ 4*z^3/27 := by
    nlinarith only [mul_nonneg (sq_nonneg (u-2*z/3)) (show 0≤u+z/3 by linarith)]
  have hpoly : 0 ≤ (2*z-1)*(19+38*z-32*z^2) := by
    refine mul_nonneg (by linarith only [hz]) ?_
    nlinarith only [hz,mul_nonneg (show 0≤z by linarith only [hz]) (sub_nonneg.mpr hz')]
  nlinarith only [hpoly,hmax]

private lemma large_bottom {l k : ℕ} {m : Masses} (hm : Valid k m)
    (hb : 5/24 ≤ score l k m) : 1/4 < m.p := by
  rcases hm with ⟨hp,hu,hv,hh,hs,_⟩
  have hrest : m.h ≤ 1 - m.p - m.u := by linarith
  have e₁ : 0 ≤ m.p*(m.v^2/(l:ℝ)+m.h^2/(k:ℝ)) := by positivity
  have e₂ := mul_le_mul_of_nonneg_left hrest (sq_nonneg m.u)
  have hupper : score l k m ≤ m.p*(1-m.p)+m.u^2*(1-2*m.p-m.u) := by
    dsimp [score]; nlinarith
  by_contra! h
  let z := 1-2*m.p
  have hz : 1/2 ≤ z := by dsimp [z]; linarith
  have hz' : z ≤ 1 := by dsimp [z]; linarith
  have htrans : m.p*(1-m.p)=(1-z^2)/4 := by dsimp [z]; ring
  change score l k m ≤ m.p*(1-m.p)+m.u^2*(z-m.u) at hupper
  rw [htrans] at hupper
  have h := hupper.trans (scalar_low z m.u hz hz' hu)
  linarith only [hb,h]

/-- All ordinary and special mass classes are occupied at the ternary-ladder
benchmark. When a bonus slot exists its aggregate mass is positive too. -/
theorem interior {l k : ℕ} (hl : 0 < l) {m : Masses} (hm : IsMax l k m)
    (hb : 5/24 ≤ score l k m) : 0 < m.p ∧ 0 < m.u ∧ 0 < m.v ∧ (0 < k → 0 < m.h) := by
  have hp := large_bottom hm.1 hb
  have hp0 : 0 < m.p := by linarith
  rcases hm.1 with ⟨hp',hu,hv,hh,hs,hzero⟩
  have hl' : 0 < (l:ℝ) := by exact_mod_cast hl
  let g := grad l k m
  have uv (hu' : 0 < m.u) : g.v ≤ g.u := by
    have h := first_order hm (⟨0,-1,1,0⟩ : Masses) hu' (by
      intro t ht ha
      dsimp [Valid,mix]
      exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,
        by intro hk; linarith [hzero hk]⟩)
    dsimp [g,dot] at *; linarith
  have vu (hv' : 0 < m.v) : g.u ≤ g.v := by
    have h := first_order hm (⟨0,1,-1,0⟩ : Masses) hv' (by
      intro t ht ha
      dsimp [Valid,mix]; exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,
        by intro hk; linarith [hzero hk]⟩)
    dsimp [g,dot] at *; linarith
  have hu' : 0 < m.u := by
    by_contra! hnot
    have he : m.u=0 := le_antisymm hnot hu
    by_cases hv' : 0<m.v
    · have h := vu hv'; dsimp [g,grad] at h; rw [he] at h
      have hq : 0 < 2*m.p*m.v/(l:ℝ) := by positivity
      ring_nf at h hq
      linarith only [h,hq]
    · have he' : m.v=0 := by linarith
      have hH : 0<m.h := by
        apply lt_of_le_of_ne hh
        intro hzeroH
        have : m.h=0 := hzeroH.symm
        dsimp [score] at hb; rw [he,he',this] at hb
        norm_num at hb
        nlinarith only [hb,hs,he,he',this]
      have hk' : 0 < (k:ℝ) := by
        have : k≠0 := fun hz => hH.ne' (hzero hz)
        exact_mod_cast Nat.pos_of_ne_zero this
      have h := first_order hm (⟨0,1,0,-1⟩ : Masses) hH (by
        intro t ht ha; dsimp [Valid,mix]
        refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
        intro hk; subst k; norm_num at hk')
      dsimp [dot,grad] at h; rw [he] at h
      nlinarith [show 0 < 2*m.p*m.h/(k:ℝ) by positivity]
  have hH' (hk : 0<k) : 0<m.h := by
    apply lt_of_le_of_ne hh
    intro hzH
    have he : m.h=0 := hzH.symm
    have h := first_order hm (⟨0,-1,0,1⟩ : Masses) hu' (by
      intro t ht ha; dsimp [Valid,mix]
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by omega⟩)
    dsimp [dot,grad] at h; simp [he] at h; nlinarith [mul_pos hp0 hu',sq_pos_of_pos hu']
  refine ⟨hp0,hu',?_,hH'⟩
  apply lt_of_le_of_ne hv
  intro hzV
  have he : m.v=0 := hzV.symm
  have hcut := uv hu'
  dsimp [g,grad] at hcut
  simp [he] at hcut
  have hE : 0 ≤ m.h-m.p := by
    exact nonneg_of_mul_nonneg_right hcut (by positivity : 0 < 2*m.u)
  have hH : 0<m.h := by linarith
  have hk : 0<k := Nat.pos_of_ne_zero (fun h => hH.ne' (hzero h))
  have hk' : 0<(k:ℝ) := by exact_mod_cast hk
  have transfer (d : Masses) {a : ℝ} (ha : 0<a)
      (h : ∀ t, 0 ≤ t → t ≤ a → Valid k (mix m d t)) :
      dot g d ≤ 0 := first_order hm d ha h
  have uh : g.h = g.u := by
    apply le_antisymm
    · have w := transfer ⟨0,-1,0,1⟩ hu' (by
        intro t ht ha; dsimp [Valid,mix]
        exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by omega⟩)
      dsimp [dot] at w; linarith
    · have w := transfer ⟨0,1,0,-1⟩ hH (by
        intro t ht ha; dsimp [Valid,mix]
        exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by omega⟩)
      dsimp [dot] at w; linarith
  have ph : g.p = g.h := by
    apply le_antisymm
    · have w := transfer ⟨1,0,0,-1⟩ hH (by
        intro t ht ha; dsimp [Valid,mix]
        exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by omega⟩)
      dsimp [dot] at w; linarith
    · have w := transfer ⟨-1,0,0,1⟩ hp0 (by
        intro t ht ha; dsimp [Valid,mix]
        exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by omega⟩)
      dsimp [dot] at w; linarith
  let q := m.h/(k:ℝ)
  have hq : 0<q := by dsimp [q]; positivity
  dsimp [g,grad] at uh ph
  simp [he] at ph
  have id₁ : m.u^2=2*m.u*(m.h-m.p)+2*m.p*q := by
    change m.u^2 = 2*m.u*(m.h-m.p)+2*m.p*(m.h/(k:ℝ))
    have hpq : 2*m.p*m.h/(k:ℝ) = 2*m.p*(m.h/(k:ℝ)) := by ring
    rw [hpq] at uh
    linarith only [uh]
  have id₂ : m.u+(m.h-m.p)=2*m.u^2+(m.h-2*m.p)*q := by
    dsimp [q]
    have h₁ : m.h^2/(k:ℝ)=m.h*(m.h/(k:ℝ)) := by ring
    have h₂ : 2*m.p*m.h/(k:ℝ)=(2*m.p)*(m.h/(k:ℝ)) := by ring
    rw [h₁,h₂] at ph; nlinarith only [ph,hs,he]
  have he' : m.h-m.p < m.u/2 := by
    by_contra hn
    have h := le_of_not_gt hn
    nlinarith only [id₁,mul_nonneg hu (show 0 ≤ 2*(m.h-m.p)-m.u by linarith only [h]),mul_pos hp0 hq]
  have hu2 : m.u < 1/2 := by linarith
  have ha : m.h-2*m.p < 0 := by linarith
  have : 2*m.u^2 < m.u := by nlinarith [mul_pos hu' (by linarith : 0 < 1-2*m.u)]
  nlinarith [mul_neg_of_neg_of_pos ha hq]


/-- Splitting an occupied ordinary slot improves the optimized score. -/
theorem add_ordinary {k : ℕ} {m : Masses} (hm : IsMax 1 k m)
    (hb : 5/24 ≤ score 1 k m) : score 1 k m < score 2 k m := by
  obtain ⟨hp,_,hv,_⟩ := interior (by decide : 0<1) hm hb
  dsimp [score]; norm_num
  nlinarith only [mul_pos hp (sq_pos_of_pos hv)]

/-- At a branching threshold one of the two equal ordinary masses can be
put on the newly opened bonus slot before re-equalizing the bonus weights. -/
theorem add_bonus {k : ℕ} {m : Masses} (hm : IsMax 2 k m)
    (hb : 5/24 ≤ score 2 k m) :
    ∃ m', Valid (k+1) m' ∧ score 2 k m < score 1 (k+1) m' := by
  obtain ⟨hp,hu,hv,_⟩ := interior (by decide : 0<2) hm hb
  obtain ⟨hp',hu',hv',hh,hs,hzero⟩ := hm.1
  let m' : Masses := ⟨m.p,m.u,m.v/2,m.h+m.v/2⟩
  refine ⟨m',⟨hp',hu',by dsimp [m']; positivity, by dsimp [m']; positivity,
    by dsimp [m']; linarith,by omega⟩,?_⟩
  have hspread : (m.v/2)^2 + (m.h+m.v/2)^2/((k:ℝ)+1) ≤
      m.v^2/2+m.h^2/(k:ℝ) := by
    by_cases h : k=0
    · rw [hzero h,h]; norm_num; nlinarith
    · have hk : 0<(k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
      have id : m.v^2/2+m.h^2/(k:ℝ)- ((m.v/2)^2 + (m.h+m.v/2)^2/((k:ℝ)+1)) =
          (2*m.h-(k:ℝ)*m.v)^2/(4*(k:ℝ)*((k:ℝ)+1)) := by
        field_simp; ring
      exact sub_nonneg.mp (id.ge.trans' (show 0 ≤ (2*m.h-(k:ℝ)*m.v)^2/(4*(k:ℝ)*((k:ℝ)+1)) by positivity))
  have hbonus : m.u^2*m.h < m.u^2*(m.h+m.v/2) := by
    nlinarith only [mul_pos (sq_pos_of_pos hu) hv]
  dsimp [score,m']
  norm_num
  nlinarith only [hbonus, mul_le_mul_of_nonneg_left hspread hp.le]

/-- A three-atom tail witnesses the benchmark in both alternating profiles. -/
theorem benchmark_double (k : ℕ) : ∃ m, Valid k m ∧ 5/24 ≤ score 2 k m := by
  refine ⟨⟨1/2,1/6,1/3,0⟩,?_,?_⟩
  · norm_num [Valid]
  · norm_num [score]

theorem benchmark_single {k : ℕ} (hk : 0<k) : ∃ m, Valid k m ∧ 5/24 ≤ score 1 k m := by
  refine ⟨⟨1/2,1/6,1/6,1/6⟩,?_,?_⟩
  · norm_num [Valid, Nat.ne_of_gt hk]
  · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have h : (1:ℝ)/(k:ℝ) ≤ 1 := (div_le_one (by linarith)).2 hk1
    dsimp [score]; norm_num
    rw [div_eq_mul_inv] at h
    simp only [one_mul] at h
    simp only [div_eq_mul_inv]
    norm_num
    linarith only [h]

#print axioms interior
#print axioms add_ordinary
#print axioms add_bonus

section Pruning
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A quadratic weighted graph score with an arbitrary vertex bonus. -/
def graphScore (E : α → α → ℝ) (b w : α → ℝ) : ℝ :=
  ∑ i, (b i*w i + ∑ j, E i j*w i*w j)

private def dir (i j x : α) : ℝ := (if x=i then 1 else 0) - (if x=j then 1 else 0)

private def slope (E : α → α → ℝ) (b w d : α → ℝ) : ℝ :=
  ∑ i, (b i*d i + ∑ j, E i j * (w i*d j+d i*w j))

omit [DecidableEq α] in
private lemma quad_expansion (E : α → α → ℝ) (b w d : α → ℝ) (s : ℝ) :
    graphScore E b (fun i => w i+s*d i) =
      graphScore E b w + s*slope E b w d + s^2*∑ i, ∑ j, E i j*d i*d j := by
  unfold graphScore slope
  simp only [Finset.mul_sum, ←Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_add s,Finset.mul_sum]
  have eqsum : (∑ j, E i j*(w i+s*d i)*(w j+s*d j)) =
      ∑ j, (E i j*w i*w j + s*(E i j*(w i*d j+d i*w j)) + s^2*(E i j*d i*d j)) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [eqsum,Finset.sum_add_distrib,Finset.sum_add_distrib]
  ring

private lemma quad_dir (E : α → α → ℝ) {i j : α}
    (hi : E i i = 0) (hj : E j j = 0) (hij : E i j = 0) (hji : E j i = 0) :
    (∑ a, ∑ b, E a b * dir i j a * dir i j b) = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  by_cases ha : a=i <;> by_cases ha' : a=j <;> by_cases hb : b=i <;> by_cases hb' : b=j <;>
    simp_all [dir]

private lemma collapse {E : α → α → ℝ} {b w : α → ℝ} (hw : ∀ i,0 ≤ w i)
    (hz : ∀ i, E i i=0) {i j : α} (hne : i≠j) (hi : 0<w i) (hj : 0<w j)
    (hij : E i j = 0) (hji : E j i = 0) :
    ∃ v : α → ℝ, (∀ i,0 ≤ v i) ∧ (∑ i,v i) = ∑ i,w i ∧
      graphScore E b w ≤ graphScore E b v ∧
      (Finset.univ.filter fun i => 0 < v i).card < (Finset.univ.filter fun i => 0 < w i).card := by
  classical
  let go (s : ℝ) (hs₁ : -w i ≤ s) (hs₂ : s ≤ w j)
      (hz' : s = -w i ∨ s = w j) (gain : 0 ≤ s*slope E b w (dir i j)) :
      ∃ v : α → ℝ, (∀ i,0 ≤ v i) ∧ (∑ i,v i) = ∑ i,w i ∧
        graphScore E b w ≤ graphScore E b v ∧
        (Finset.univ.filter fun i => 0 < v i).card < (Finset.univ.filter fun i => 0 < w i).card := by
    let v (x : α) := w x + s*dir i j x
    have vi : v i=w i+s := by simp [v,dir,hne]
    have vj : v j=w j-s := by simp [v,dir,hne.symm,sub_eq_add_neg]
    have oth (x : α) (hxi : x≠i) (hxj : x≠j) : v x=w x := by simp [v,dir,hxi,hxj]
    have nonneg (x : α) : 0≤v x := by
      by_cases hxi : x=i
      · rw [hxi,vi]; linarith
      by_cases hxj : x=j
      · rw [hxj,vj]; linarith
      exact (oth x hxi hxj).ge.trans' (hw x)
    have total : (∑ x,v x)=∑ x,w x := by
      simp [v,dir,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_sub_distrib]
    have improvement : graphScore E b w ≤ graphScore E b v := by
      dsimp [v]; rw [quad_expansion,quad_dir E (hz i) (hz j) hij hji]; linarith
    have sub : (Finset.univ.filter fun a => 0<v a) ⊆ (Finset.univ.filter fun a => 0<w a) := by
      intro x h
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at h ⊢
      by_cases hxi : x=i
      · simpa [hxi] using hi
      by_cases hxj : x=j
      · simpa [hxj] using hj
      rwa [←oth x hxi hxj]
    have witness : ∃ x, 0<w x ∧ v x=0 := by
      cases hz' with
      | inl h => exact ⟨i,hi, by rw [vi,h]; ring⟩
      | inr h => exact ⟨j,hj, by rw [vj,h]; ring⟩
    obtain ⟨x,hx,hvx⟩ := witness
    have strict := Finset.ssubset_iff_subset_ne.mpr ⟨sub, by
      intro he
      have : x ∈ Finset.univ.filter (fun a => 0<v a) := he.symm ▸
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
      simpa [hvx] using (Finset.mem_filter.mp this).2⟩
    exact ⟨v,nonneg,total,improvement,Finset.card_lt_card strict⟩
  by_cases h : 0 ≤ slope E b w (dir i j)
  · exact go (w j) (by linarith) le_rfl (Or.inr rfl) (mul_nonneg hj.le h)
  · exact go (-w i) le_rfl (by linarith) (Or.inl rfl) (mul_nonneg_of_nonpos_of_nonpos
      (by linarith) (le_of_not_ge h))

/-- Weighted Motzkin--Straus elimination with vertex bonuses. There exists
a score-preserving-or-better redistribution supported on mutually compatible
vertices. Symmetry and positivity of the edge coefficients are unnecessary. -/
theorem prune (E : α → α → ℝ) (b w : α → ℝ) (hz : ∀ i, E i i=0) (hw : ∀ i,0 ≤ w i) :
    ∃ v : α → ℝ, (∀ i,0 ≤ v i) ∧ (∑ i,v i)=∑ i,w i ∧ graphScore E b w ≤ graphScore E b v ∧
      ∀ i j, i≠j → 0<v i → 0<v j → E i j ≠ 0 ∨ E j i ≠ 0 := by
  classical
  let size (u : α → ℝ) := (Finset.univ.filter fun i => 0<u i).card
  induction h : size w using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases done : ∀ i j, i≠j → 0<w i → 0<w j → E i j ≠ 0 ∨ E j i ≠ 0
    · exact ⟨w,hw,rfl,le_rfl,done⟩
    push_neg at done
    obtain ⟨i,j,hne,hi,hj,hij,hji⟩ := done
    obtain ⟨v,hv,hvsum,hvscore,hvsize⟩ := collapse hw hz hne hi hj hij hji
    have hn : size v < n := h ▸ hvsize
    obtain ⟨u,hu,huSum,huScore,hdone⟩ := ih _ hn v hv rfl
    exact ⟨u,hu,huSum.trans hvsum,hvscore.trans huScore,hdone⟩

#print axioms prune
end Pruning

/-- A support avoiding neighbors in an interval of length 2k occupies at
most k labels, by pairing consecutive labels from the left endpoint. -/
theorem path_capacity (S : Finset ℕ) (a k : ℕ)
    (hb : ∀ x ∈ S, a ≤ x ∧ x < a+2*k) (hi : ∀ x ∈ S, x+1 ∉ S) : S.card ≤ k := by
  rw [←Finset.card_range k]
  apply Finset.card_le_card_of_injOn (fun x => (x-a)/2)
  · intro x hx
    have := hb x hx
    simp only [Finset.mem_range]
    omega
  · intro x hx y hy h
    change x∈S at hx
    change y∈S at hy
    change (x-a)/2=(y-a)/2 at h
    have bx := hb x hx
    have by' := hb y hy
    by_contra neq
    rcases (show x+1=y ∨ y+1=x by omega) with rfl|rfl
    · exact hi x hx hy
    · exact hi y hy hx

/-- In a tail of length 2k+1, only the initial vertex has no bonus, so
at most k supported vertices can receive a bonus. -/
theorem odd_path_high_capacity (S : Finset ℕ) (k : ℕ)
    (hb : ∀ x ∈ S, x < 2*k+1) (hi : ∀ x ∈ S, x+1 ∉ S) : (S.erase 0).card ≤ k := by
  apply path_capacity _ 1 k
  · intro x hx
    obtain ⟨h,h'⟩ := Finset.mem_erase.mp hx
    have := hb x h'
    omega
  · intro x hx h
    exact hi x (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase h)

/-- An aggregate spread over at most n slots has squared `ℓ²` mass
at least its squared total divided by n. -/
theorem equalization {α : Type*} (S : Finset α) (w : α → ℝ) {n : ℕ} (h : S.card ≤ n) :
    (∑ i ∈ S, w i)^2/(n:ℝ) ≤ ∑ i ∈ S, (w i)^2 := by
  have pos : 0 ≤ ∑ i ∈ S, (w i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg (w i)
  by_cases hz : n=0
  · simpa [hz] using pos
  · have hn : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hc : (S.card:ℝ) ≤ n := by exact_mod_cast h
    apply (div_le_iff₀ hn).mpr
    have hh := Finset.sum_mul_sq_le_sq_mul_sq S w (fun _ => (1:ℝ))
    simp only [mul_one,one_pow,Finset.sum_const, nsmul_eq_mul,mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hc pos)


/-- Ordered edge coefficient on the interleaved tail. -/
def pathCoeff {n : ℕ} (p : ℝ) (i j : Fin n) : ℝ :=
  if i.val+1 < j.val ∨ j.val+1 < i.val then p else 0

/-- Cubic probability after splitting the first three ranks from the tail. -/
noncomputable def pathRaw {n : ℕ} (p u t : ℝ) (w : Fin n → ℝ) : ℝ :=
  p^2*(1-p) + 2*p*u*(t+∑ i,w i) + 2*p*t*(∑ i,w i) +
    graphScore (pathCoeff p) (fun i => if i.val=0 then 0 else u^2) w

def PathValid {n : ℕ} (p u t : ℝ) (w : Fin n → ℝ) : Prop :=
  0≤p ∧ 0≤u ∧ 0≤t ∧ (∀ i,0≤w i) ∧ p+u+t+(∑ i,w i)=1

def Separated {n : ℕ} (w : Fin n → ℝ) : Prop :=
  ∀ i j, 0<w i → 0<w j → i.val+1 ≠ j.val

theorem path_prune {n : ℕ} {p u t : ℝ} {w : Fin n → ℝ} (hw : PathValid p u t w) :
    ∃ v : Fin n → ℝ, PathValid p u t v ∧ pathRaw p u t w ≤ pathRaw p u t v ∧ Separated v := by
  let b (i : Fin n) := if i.val=0 then (0:ℝ) else u^2
  obtain ⟨v,hv,hs,hscore,hcl⟩ := prune (pathCoeff p) b w (fun i => by simp [pathCoeff]) hw.2.2.2.1
  refine ⟨v, ⟨hw.1,hw.2.1,hw.2.2.1,hv,hs ▸ hw.2.2.2.2⟩,?_,?_⟩
  · dsimp [pathRaw]
    rw [hs]
    exact add_le_add_left hscore _
  · intro i j hi hj he
    have hn : i≠j := by intro hij; subst j; omega
    have h₁ : ¬(i.val+1 < j.val ∨ j.val+1 < i.val) := by omega
    have h₂ : ¬(j.val+1 < i.val ∨ i.val+1 < j.val) := by omega
    simpa [pathCoeff,h₁,h₂] using hcl i j hn hi hj

noncomputable def bonusMass {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  ∑ i, if i.val=0 then 0 else w i

/-- For separated tail support, every pair of distinct occupied tail
slots is compatible. Only their squared masses and bonus total survive. -/
theorem pathRaw_of_separated {n : ℕ} {p u t : ℝ} {w : Fin n → ℝ}
    (hw : PathValid p u t w) (hs : Separated w) :
    pathRaw p u t w = p*(1-p) - p*(u^2+t^2+∑ i,(w i)^2) + u^2*bonusMass w := by
  classical
  have point (i j : Fin n) : pathCoeff p i j*w i*w j =
      p*(w i*w j) - (if i=j then p*(w i)^2 else 0) := by
    by_cases he : i=j
    · subst j; simp [pathCoeff]; ring
    rw [if_neg he, sub_zero]
    by_cases hz : w i=0
    · simp [hz]
    by_cases hz' : w j=0
    · simp [hz']
    have h₁ := hs i j (lt_of_le_of_ne (hw.2.2.2.1 i) (Ne.symm hz)) (lt_of_le_of_ne (hw.2.2.2.1 j) (Ne.symm hz'))
    have h₂ := hs j i (lt_of_le_of_ne (hw.2.2.2.1 j) (Ne.symm hz')) (lt_of_le_of_ne (hw.2.2.2.1 i) (Ne.symm hz))
    have hn : i.val≠j.val := fun h => he (Fin.ext h)
    rw [pathCoeff,if_pos (show i.val+1 < j.val ∨ j.val+1 < i.val by omega)]
    ring
  have coef (i : Fin n) : (if i.val=0 then 0 else u^2)*w i = u^2*(if i.val=0 then 0 else w i) := by split <;> simp
  have row (i : Fin n) : (∑ j,pathCoeff p i j*w i*w j)=p*(w i*(∑ j,w j))-p*(w i)^2 := by
    simp_rw [point]
    simp [Finset.sum_sub_distrib,←Finset.mul_sum]
  have g : graphScore (pathCoeff p) (fun i => if i.val=0 then 0 else u^2) w =
      u^2*bonusMass w + p*((∑ i,w i)*(∑ j,w j)) - p*(∑ i,(w i)^2) := by
    unfold graphScore bonusMass
    simp_rw [row,coef]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [←Finset.mul_sum,←Finset.sum_mul]
    ring
  unfold pathRaw
  rw [g]
  have tot := hw.2.2.2.2
  rw [show (∑ i,w i)=1-p-u-t by linarith only [tot]]
  ring


/-- Cauchy--Schwarz for a separated segment of the interleaved tail. -/
private theorem segment_bound {n : ℕ} {w : Fin n → ℝ}
    (hw : ∀ i,0≤w i) (hs : Separated w) (a k : ℕ) (hn : n ≤ a+2*k) :
    (∑ i, if a ≤ i.val then w i else 0)^2/(k:ℝ) ≤
      ∑ i, if a ≤ i.val then (w i)^2 else 0 := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ 0<w i)
  have hS (i : Fin n) : i∈S ↔ a ≤ i.val ∧ 0<w i := by simp [S]
  have card : S.card≤k := by
    rw [←Finset.card_range k]
    apply Finset.card_le_card_of_injOn (fun i : Fin n => (i.val-a)/2)
    · intro i hi
      have h := (hS i).mp hi
      have hb := i.isLt
      simp only [Finset.mem_range]
      omega
    · intro i hi j hj h
      obtain ⟨bi,wi⟩ := (hS i).mp hi
      obtain ⟨bj,wj⟩ := (hS j).mp hj
      change (i.val-a)/2=(j.val-a)/2 at h
      have h₁ := hs i j wi wj
      have h₂ := hs j i wj wi
      exact Fin.ext (by omega)
  have tr (f : ℝ → ℝ) (hf : f 0=0) :
      (∑ i ∈ S, f (w i))=∑ i, if a ≤ i.val then f (w i) else 0 := by
    dsimp [S]; rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases ha : a ≤ i.val
    · by_cases hp : 0<w i
      · simp [ha,hp]
      · have hz : w i=0 := le_antisymm (le_of_not_gt hp) (hw i)
        simp [ha,hz,hf]
    · simp [ha]
  have key := equalization S w card
  have tr1 := tr (fun z => z) rfl
  have tr2 := tr (fun z => z^2) (by norm_num)
  dsimp at tr1 tr2
  rw [tr1,tr2] at key
  exact key

private theorem first_sum {k : ℕ} (w : Fin (2*k+1) → ℝ) :
    (∑ i, w i) = w 0 + (∑ i, if i.val=0 then 0 else w i) := by
  classical
  have aux (i : Fin (2*k+1)) : w i = (if i=0 then w 0 else 0)+(if i.val=0 then 0 else w i) := by
    by_cases h : i=0
    · simp [h]
    · have h' : i.val≠0 := fun a => h (Fin.ext a)
      simp [h,h']
  calc
    _ = ∑ i, ((if i=0 then w 0 else 0)+(if i.val=0 then 0 else w i)) := Finset.sum_congr rfl fun i _ => aux i
    _ = _ := by simp [Finset.sum_add_distrib]

/-- In an even tail all surviving tail mass can be assigned bonus slots. -/
theorem even_upper {k : ℕ} {p u t : ℝ} {w : Fin (2*k) → ℝ} (hw : PathValid p u t w) :
    ∃ m, Valid k m ∧ pathRaw p u t w ≤ score 1 k m := by
  obtain ⟨v,hv,im,hs⟩ := path_prune hw
  have hsq := segment_bound hv.2.2.2.1 hs 0 k (by omega)
  simp only [Nat.zero_le,if_true] at hsq
  let m : Masses := ⟨p,u,t,∑ i,v i⟩
  have hm : Valid k m := by
    dsimp [Valid,m]
    refine ⟨hv.1,hv.2.1,hv.2.2.1,Finset.sum_nonneg (fun i _ => hv.2.2.2.1 i), hv.2.2.2.2,?_⟩
    rintro rfl
    apply Finset.sum_eq_zero
    intro i _
    have := i.isLt; omega
  have hbonus : bonusMass v ≤ ∑ i,v i := by
    unfold bonusMass
    apply Finset.sum_le_sum
    intro i _
    split
    · exact hv.2.2.2.1 i
    · exact le_rfl
  refine ⟨m,hm,im.trans ?_⟩
  rw [pathRaw_of_separated hv hs]
  dsimp [score,m]
  norm_num
  nlinarith only [mul_le_mul_of_nonneg_left hsq hv.1, mul_le_mul_of_nonneg_left hbonus (sq_nonneg u)]

/-- For an odd tail rank zero joins the ordinary pool and every other
surviving weight can be assigned one of k bonus slots. -/
theorem odd_upper {k : ℕ} {p u t : ℝ} {w : Fin (2*k+1) → ℝ} (hw : PathValid p u t w) :
    ∃ m, Valid k m ∧ pathRaw p u t w ≤ score 2 k m := by
  obtain ⟨v,hv,im,hs⟩ := path_prune hw
  have hsq := segment_bound hv.2.2.2.1 hs 1 k (by omega)
  have conv (f : Fin (2*k+1) → ℝ) (i : Fin (2*k+1)) :
      (if 1 ≤ i.val then f i else 0)=(if i.val=0 then 0 else f i) := by
    by_cases h : i.val=0 <;> simp [h,show 1 ≤ i.val ↔ i.val≠0 by omega]
  change (∑ i, if 1 ≤ i.val then v i else 0)^2/(k:ℝ) ≤
    ∑ i, if 1 ≤ i.val then (fun x => (v x)^2) i else 0 at hsq
  simp_rw [conv v, conv (fun i => (v i)^2)] at hsq
  have hsum := first_sum v
  have hsum2 := first_sum (fun i => (v i)^2)
  let m : Masses := ⟨p,u,t+v 0,bonusMass v⟩
  have hm : Valid k m := by
    refine ⟨hv.1,hv.2.1,add_nonneg hv.2.2.1 (hv.2.2.2.1 0),?_,?_,?_⟩
    · dsimp [m,bonusMass]
      apply Finset.sum_nonneg
      intro i _
      split
      · exact le_rfl
      · exact hv.2.2.2.1 i
    · dsimp [m,bonusMass]; linarith only [hsum,hv.2.2.2.2]
    · rintro rfl
      dsimp [m,bonusMass]
      apply Finset.sum_eq_zero
      intro i _
      have := i.isLt
      simp [show i.val=0 by omega]
  refine ⟨m,hm,im.trans ?_⟩
  rw [pathRaw_of_separated hv hs]
  dsimp [score,m,bonusMass]
  have cs : (t+v 0)^2/2 ≤ t^2+(v 0)^2 := by nlinarith [sq_nonneg (t-v 0)]
  nlinarith only [mul_le_mul_of_nonneg_left (add_le_add cs hsq) hv.1,congrArg (fun x => p*x) hsum2]


private theorem block_realize {n k : ℕ} (L H : Finset (Fin n))
    (hk : H.card=k) (hL : ∀ i∈L, i.val=0) (hH : ∀ i∈H, 0 < i.val)
    (hsep : ∀ i∈L ∪ H, ∀ j∈L ∪ H, i.val+1≠j.val)
    (m : Masses) (hm : Valid k m) :
    ∃ (t : ℝ) (w : Fin n → ℝ), PathValid m.p m.u t w ∧ pathRaw m.p m.u t w = score (L.card+1) k m := by
  classical
  let q := m.v/((L.card:ℝ)+1)
  let r := m.h/(k:ℝ)
  let w (i : Fin n) := (if i∈L then q else 0) + (if i∈H then r else 0)
  have q0 : 0≤q := by dsimp [q]; exact div_nonneg hm.2.2.1 (by positivity)
  have r0 : 0≤r := by dsimp [r]; exact div_nonneg hm.2.2.2.1 (by positivity)
  have w0 (i : Fin n) : 0≤w i := by
    dsimp [w]; split <;> split <;> linarith
  have dis (i : Fin n) (hi : i∈L) : i∉H := fun hh => by
    have := hL i hi
    have := hH i hh
    omega
  have summ (X : Finset (Fin n)) (x : ℝ) :
      (∑ i : Fin n, if i∈X then x else 0) = (X.card:ℝ)*x := by
    rw [← Finset.sum_filter]
    simp
  have vals : (∑ i,w i) = (L.card:ℝ)*q + (k:ℝ)*r := by
    unfold w; rw [Finset.sum_add_distrib,summ,summ,hk]
  have sqpt (i : Fin n) : (w i)^2 = (if i∈L then q^2 else 0)+(if i∈H then r^2 else 0) := by
    by_cases hl : i∈L
    · simp [w,hl,dis i hl]
    · by_cases hh : i∈H <;> simp [w,hl,hh]
  have squares : (∑ i,(w i)^2) = (L.card:ℝ)*q^2 + (k:ℝ)*r^2 := by
    simp_rw [sqpt]; rw [Finset.sum_add_distrib,summ,summ,hk]
  have bonuses : bonusMass w = (k:ℝ)*r := by
    dsimp [bonusMass]
    calc
      _ = ∑ i : Fin n, if i∈H then r else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hl : i∈L
        · simp [w,hl,hL i hl,dis i hl]
        · by_cases hh : i∈H
          · simp [w,hl,hh,Nat.ne_of_gt (hH i hh)]
          · simp [w,hl,hh]
      _ = _ := by rw [summ,hk]
  have qr : ((L.card:ℝ)+1)*q=m.v := by
    dsimp [q]; field_simp
  have rr : (k:ℝ)*r=m.h := by
    by_cases h : k=0
    · simp [h,hm.2.2.2.2.2 h]
    · dsimp [r]; field_simp
  have valid : PathValid m.p m.u q w := by
    refine ⟨hm.1,hm.2.1,q0,w0,?_⟩
    rw [vals]
    nlinarith only [qr,rr,hm.2.2.2.2.1]
  have supp (i : Fin n) (hi : 0<w i) : i∈L ∪ H := by
    by_cases hl : i∈L
    · exact Finset.mem_union_left _ hl
    by_cases hh : i∈H
    · exact Finset.mem_union_right _ hh
    simp [w,hl,hh] at hi
  refine ⟨q,w,valid,?_⟩
  rw [pathRaw_of_separated valid (fun i j hi hj => hsep i (supp i hi) j (supp j hj)),squares,bonuses,rr]
  dsimp [score]
  push_cast
  have esq : q^2+((L.card:ℝ)*q^2+(k:ℝ)*r^2)=m.v^2/((L.card:ℝ)+1)+m.h^2/(k:ℝ) := by
    have eq : m.v*q=m.v^2/((L.card:ℝ)+1) := by dsimp [q]; ring
    have er : m.h*r=m.h^2/(k:ℝ) := by dsimp [r]; ring
    nlinarith only [eq,er,congrArg (fun z => z*q) qr,congrArg (fun z => z*r) rr]
  linarith only [congrArg (fun z => m.p*z) esq]

/-- Choose every second path vertex starting at offset d. -/
private def spaced (k n d : ℕ) (hb : ∀ i : Fin k, 2*i.val+d<n) : Finset (Fin n) :=
  Finset.univ.map ⟨fun i => ⟨2*i.val+d,hb i⟩,fun i j h => Fin.ext (by
    have hv := congrArg Fin.val h
    change 2*i.val+d=2*j.val+d at hv
    omega)⟩

private theorem mem_spaced {k n d : ℕ} {hb : ∀ i : Fin k, 2*i.val+d<n} {i : Fin n} :
    i∈spaced k n d hb ↔ ∃ j : Fin k, i.val=2*j.val+d := by
  constructor
  · intro h
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp h
    exact ⟨j,rfl⟩
  · rintro ⟨j,hj⟩
    exact Finset.mem_map.mpr ⟨j,Finset.mem_univ _,Fin.ext hj.symm⟩

theorem even_realize (k : ℕ) (m : Masses) (hm : Valid k m) :
    ∃ (t : ℝ) (w : Fin (2*k) → ℝ), PathValid m.p m.u t w ∧ pathRaw m.p m.u t w=score 1 k m := by
  have hb (i : Fin k) : 2*i.val+1<2*k := by have := i.isLt; omega
  let H := spaced k (2*k) 1 hb
  have h := block_realize (∅ : Finset (Fin (2*k))) H (by simp [H,spaced]) (by simp) (by
    intro i hi
    obtain ⟨j,hj⟩ := mem_spaced.mp hi
    omega) (by
    simp only [Finset.empty_union]
    intro i hi j hj
    obtain ⟨a,ha⟩ := mem_spaced.mp hi
    obtain ⟨b,hb'⟩ := mem_spaced.mp hj
    omega) m hm
  simpa using h

theorem odd_realize (k : ℕ) (m : Masses) (hm : Valid k m) :
    ∃ (t : ℝ) (w : Fin (2*k+1) → ℝ), PathValid m.p m.u t w ∧ pathRaw m.p m.u t w=score 2 k m := by
  have hb (i : Fin k) : 2*i.val+2 < 2*k+1 := by have := i.isLt; omega
  let H := spaced k (2*k+1) 2 hb
  have h := block_realize ({0} : Finset (Fin (2*k+1))) H (by simp [H,spaced])
    (by simp) (by
      intro i hi
      obtain ⟨j,hj⟩ := mem_spaced.mp hi
      omega) (by
      intro i hi j hj
      simp only [Finset.mem_union,Finset.mem_singleton] at hi hj
      have even (a : Fin (2*k+1)) (ha : a=0 ∨ a∈H) : ∃ b : ℕ,a.val=2*b := by
        rcases ha with rfl|h
        · exact ⟨0,rfl⟩
        · obtain ⟨b,hb'⟩ := mem_spaced.mp h
          exact ⟨b.val+1,by omega⟩
      obtain ⟨a,ha⟩ := even i hi
      obtain ⟨b,hb'⟩ := even j hj
      omega) m hm
  simpa using h


/-- The feasible scores for a tail with n alternating ranks. -/
def PathValues (n : ℕ) : Set ℝ :=
  {b | ∃ (p u t : ℝ) (w : Fin n → ℝ), PathValid p u t w ∧ pathRaw p u t w=b}

private theorem attain_profile {l k n : ℕ} {b : ℝ} (hb : IsGreatest (PathValues n) b)
    (upper : ∀ {p u t : ℝ} {w : Fin n → ℝ}, PathValid p u t w →
      ∃ m, Valid k m ∧ pathRaw p u t w ≤ score l k m)
    (realize : ∀ m, Valid k m → ∃ (t : ℝ) (w : Fin n → ℝ), PathValid m.p m.u t w ∧
      pathRaw m.p m.u t w=score l k m) :
    ∃ m, IsMax l k m ∧ score l k m=b := by
  obtain ⟨p,u,t,w,hw,hb'⟩ := hb.1
  obtain ⟨m,hm,hscore⟩ := upper hw
  have ub (x : Masses) (hx : Valid k x) : score l k x ≤ b := by
    obtain ⟨t',w',hw',he⟩ := realize x hx
    exact hb.2 ⟨x.p,x.u,t',w',hw',he⟩
  have eq := le_antisymm (ub m hm) (hb' ▸ hscore)
  exact ⟨m,⟨hm,fun y hy => eq ▸ ub y hy⟩,eq⟩

/-- Adding a single tail rank strictly increases the extremal probability
at every positive length. -/
theorem path_step_strict {n : ℕ} {b d : ℝ} (hn : 0<n) (hb : IsGreatest (PathValues n) b)
    (hd : IsGreatest (PathValues (n+1)) d) : b<d := by
  let k := n/2
  have dich : n=2*k ∨ n=2*k+1 := by dsimp [k]; omega
  clear_value k
  rcases dich with rfl|rfl
  · obtain ⟨m,hm,he⟩ := attain_profile hb (@even_upper k) (even_realize k)
    obtain ⟨x,hx,hx'⟩ := benchmark_single (by omega : 0<k)
    have better := add_ordinary hm (hx'.trans (hm.2 x hx))
    obtain ⟨t,w,hw,hw'⟩ := odd_realize k m hm.1
    have high := hd.2 ⟨m.p,m.u,t,w,hw,hw'⟩
    exact he ▸ better.trans_le high
  · obtain ⟨m,hm,he⟩ := attain_profile hb (@odd_upper k) (odd_realize k)
    obtain ⟨x,hx,hx'⟩ := benchmark_double k
    obtain ⟨m',hm',better⟩ := add_bonus hm (hx'.trans (hm.2 x hx))
    obtain ⟨t,w,hw,hw'⟩ := even_realize (k+1) m' hm'
    rw [show 2*k+1+1=2*(k+1) by omega] at hd
    have high := hd.2 ⟨m'.p,m'.u,t,w,hw,hw'⟩
    exact he ▸ better.trans_le high

#print axioms path_step_strict

end OneScale.Tail
