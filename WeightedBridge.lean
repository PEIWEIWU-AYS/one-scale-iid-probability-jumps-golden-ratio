import OneScaleMenu
import CollisionLimit

open Finset
open scoped BigOperators
noncomputable section
namespace OneScale.WeightedBridge

private def bit (p : Prop) [Decidable p] : ℝ := if p then 1 else 0
private def near (c a b : ℝ) : Prop := a < c*b ∧ b < c*a
private def tight (c a b d : ℝ) : Prop := near c a b ∧ near c b d ∧ near c d a
private def core (c a b d : ℝ) : ℝ := by
  classical exact bit (tight c a b d ∧ a+b<c*d)
private def bad (c a b : ℝ) : ℝ := bit (c*a≤b)

private def avg {n : ℕ} (k : Fin n → Fin n → Fin n → ℝ) (w : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ l, w i*w j*w l*k i j l

private def part {n : ℕ} (k : ℝ → ℝ → ℝ → ℝ) (x w : Fin n → ℝ) :=
  avg (fun i j l => k (x i) (x j) (x l)) w

def spread {n : ℕ} (c : ℝ) (x w : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, w i*w j*bad c (x i) (x j)

private def pushTo {n : ℕ} (u v : Fin n) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i=u then w u+w v else if i=v then 0 else w i

private lemma push_mass {n : ℕ} {w : Fin n → ℝ} (hw : Mass w) {u v : Fin n} (huv : u≠v) :
    Mass (pushTo u v w) := by
  classical
  constructor
  · intro i; unfold pushTo; split_ifs <;> first | exact add_nonneg (hw.1 _) (hw.1 _) | exact le_rfl | exact hw.1 _
  · have eq (i : Fin n) : pushTo u v w i =
        w i + (if i=u then w v else 0) - (if i=v then w v else 0) := by
      by_cases hi : i=u <;> by_cases hj : i=v <;> simp_all [pushTo]
    simp_rw [eq]
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hw.2]
    simp

private lemma near_symm {c a b : ℝ} (h : near c a b) : near c b a := h.symm

private lemma both_in {c : ℝ} {a b d u v : ℝ} (h : tight c a b d)
    (hu : u=a ∨ u=b ∨ u=d) (hv : v=a ∨ v=b ∨ v=d) (hc : 1<c)
    (hpos : 0<u) : near c u v := by
  rcases h with ⟨h₁,h₂,h₃⟩
  have self : near c u u := by have hh := mul_lt_mul_of_pos_right hc hpos; exact ⟨by linarith,by linarith⟩
  rcases hu with hu|hu|hu <;> rcases hv with hv|hv|hv <;>
    subst_vars <;> first | assumption | apply near_symm; assumption

private lemma merge_term {n : ℕ} {c : ℝ} (hc : 1<c) (x w : Fin n → ℝ)
    (hx : ∀ i, 0<x i) (hw : ∀ i, 0≤w i) {a b : Fin n}
    (hbad : ¬near c (x a) (x b)) (hab : a≠b) (i j k : Fin n) :
    (w a+w b)*(w i*w j*w k*core c (x i) (x j) (x k)) ≤
    w a*(pushTo a b w i*pushTo a b w j*pushTo a b w k*core c (x i) (x j) (x k)) +
    w b*(pushTo b a w i*pushTo b a w j*pushTo b a w k*core c (x i) (x j) (x k)) := by
  classical
  by_cases h : tight c (x i) (x j) (x k) ∧ x i+x j<c*x k
  · simp only [core,bit,if_pos h,mul_one]
    have ex : ¬ ((i=a ∨ j=a ∨ k=a) ∧ (i=b ∨ j=b ∨ k=b)) := by
      rintro ⟨hl,hr⟩
      apply hbad
      refine both_in h.1 ?_ ?_ hc (hx a)
      · rcases hl with h|h|h <;> subst_vars <;> simp
      · rcases hr with h|h|h <;> subst_vars <;> simp
    have posA := hw a; have posB := hw b; have posi := hw i; have posj := hw j; have posk := hw k
    by_cases ia:i=a <;> by_cases ja:j=a <;> by_cases ka:k=a <;>
      by_cases ib:i=b <;> by_cases jb:j=b <;> by_cases kb:k=b <;>
      simp_all only [pushTo, or_true, true_or, or_false, false_or, if_true, if_false,
        and_true, true_and, and_false, false_and, not_true_eq_false, not_false_eq_true,
        mul_zero, zero_mul, add_zero, zero_add, not_false_iff] <;>
      subst_vars <;> simp_all [pushTo] <;> apply sub_nonneg.mp <;> ring_nf <;> try positivity
    all_goals repeat first | apply add_nonneg | apply mul_nonneg
    all_goals first
      | exact hw _
      | exact pow_nonneg (hw _) _
      | exact mul_nonneg (pow_nonneg (hw _) _) (pow_nonneg (hw _) _)
      | exact mul_nonneg (pow_nonneg (hw _) _) (hw _)
      | exact mul_nonneg (mul_nonneg (pow_nonneg (hw _) _) (hw _)) (hw _)
      | norm_num
    all_goals first
      | exact mul_nonneg (pow_nonneg (hw _) _) (pow_nonneg (hw _) _)
      | exact mul_nonneg (pow_nonneg (hw _) _) (hw _)
  · simp [core,bit,h]

private lemma merge_nondec {n : ℕ} {c : ℝ} (hc : 1<c) (x w : Fin n → ℝ)
    (hx : ∀ i, 0<x i) (hw : Mass w) {a b : Fin n} (ha : 0<w a) (hb : 0<w b)
    (hbad : ¬near c (x a) (x b)) (hab : a≠b) :
    part (core c) x w ≤ part (core c) x (pushTo a b w) ∨
    part (core c) x w ≤ part (core c) x (pushTo b a w) := by
  have hh : (w a+w b)*part (core c) x w ≤
      w a*part (core c) x (pushTo a b w)+w b*part (core c) x (pushTo b a w) := by
    unfold part avg
    simp_rw [Finset.mul_sum]
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      Finset.sum_le_sum fun k _ => merge_term hc x w hx hw.1 hbad hab i j k
  by_contra! h
  nlinarith [mul_lt_mul_of_pos_left h.1 ha,mul_lt_mul_of_pos_left h.2 hb]


private def active {n : ℕ} (w : Fin n → ℝ) := univ.filter (fun i => 0<w i)

private lemma fewer {n : ℕ} {w : Fin n → ℝ} {a b : Fin n} (ha : 0<w a)
    (hb : 0<w b) (hab : a≠b) : (active (pushTo a b w)).card < (active w).card := by
  apply card_lt_card
  refine (ssubset_iff_of_subset ?_).mpr ?_
  · intro i hi
    have hh : 0<pushTo a b w i := (mem_filter.mp hi).2
    by_cases ea : i=a
    · subst i; simpa [active] using ha
    · by_cases eb : i=b
      · simp [pushTo,ea,eb,hab.symm] at hh
      · simpa [active,pushTo,ea,eb] using hh
  · exact ⟨b,by simp [active,hb],by simp [active,pushTo,hab.symm]⟩

private lemma clique_core_bound {n : ℕ} {c : ℝ} (hc : 1<c) (x w : Fin n → ℝ)
    (hx : ∀ i, 0<x i) (hw : Mass w)
    (hnear : ∀ i, 0<w i → ∀ j, 0<w j → near c (x i) (x j)) :
    part (core c) x w ≤ beta c := by
  classical
  have hp : (active w).Nonempty := by
    obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (show (∑ i,w i)≠0 by rw [hw.2]; norm_num)
    exact ⟨i,by simpa [active] using lt_of_le_of_ne (hw.1 i) (Ne.symm hi)⟩
  obtain ⟨m,hm,hmin⟩ := Finset.exists_min_image (active w) x hp
  let y (i : Fin n) := if 0<w i then x i/x m else 1
  have hcfg : Cfg c y := by
    intro i
    by_cases h : 0 < w i
    · simp only [y,if_pos h]
      exact ⟨(one_le_div (hx m)).mpr (hmin i (by simp [active,h])),
        (div_lt_iff₀ (hx m)).mpr (hnear i h m (mem_filter.mp hm).2).1⟩
    · simp [y,h,hc]
  have hle : part (core c) x w ≤ score c y w := by
    unfold part avg score
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
    by_cases hi : 0<w i <;> by_cases hj : 0<w j <;> by_cases hk : 0<w k
    all_goals try have h0 : w i=0 := le_antisymm (le_of_not_gt hi) (hw.1 _); simp [h0]
    all_goals try have h0 : w j=0 := le_antisymm (le_of_not_gt hj) (hw.1 _); simp [h0]
    all_goals try have h0 : w k=0 := le_antisymm (le_of_not_gt hk) (hw.1 _); simp [h0]
    have he : Win c y i j k ↔ x i+x j<c*x k := by
      dsimp [Win,y]
      rw [if_pos hi,if_pos hj,if_pos hk,←add_div,←mul_div_assoc,div_lt_div_iff_of_pos_right (hx m)]
    by_cases h : tight c (x i) (x j) (x k) <;> by_cases h' : x i+x j<c*x k <;>
      simp [core,bit,h,h',he,mul_nonneg,hw.1]
  exact hle.trans (le_csSup (bdd_values c) ⟨n,y,w,hcfg,hw,rfl⟩)

private theorem core_le_beta {n : ℕ} {c : ℝ} (hc : 1<c) (x w : Fin n → ℝ)
    (hx : ∀ i, 0<x i) (hw : Mass w) : part (core c) x w ≤ beta c := by
  classical
  suffices h : ∀ N : ℕ, ∀ u : Fin n → ℝ, (active u).card ≤ N →
      Mass u → part (core c) x u ≤ beta c from h _ _ le_rfl hw
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro u hN hu
    by_cases hf : ∀ a, 0<u a → ∀ b, 0<u b → near c (x a) (x b)
    · exact clique_core_bound hc x u hx hu hf
    push_neg at hf
    obtain ⟨a,ha,b,hb,hab⟩ := hf
    have hne : a≠b := by
      rintro rfl
      have h := mul_lt_mul_of_pos_right hc (hx a)
      exact hab ⟨by linarith,by linarith⟩
    rcases merge_nondec hc x u hx hu ha hb hab hne with h|h
    · exact h.trans (ih _ ((fewer ha hb hne).trans_le hN) _ le_rfl (push_mass hu hne))
    · exact h.trans (ih _ ((fewer hb ha hne.symm).trans_le hN) _ le_rfl (push_mass hu hne.symm))

private lemma core_nonnegative_support {n : ℕ} {c : ℝ} (hc : 1<c) (x w : Fin n → ℝ)
    (hx : ∀ i, 0≤x i) (hw : Mass w) : part (core c) x w ≤ beta c := by
  let y (i : Fin n) := if 0<x i then x i else 1
  have hy (i : Fin n) : 0<y i := by dsimp [y]; split_ifs <;> first | assumption | norm_num
  refine le_trans ?_ (core_le_beta hc y w hy hw)
  unfold part avg
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (hw.1 _) (hw.1 _)) (hw.1 _))
  by_cases h : tight c (x i) (x j) (x k) ∧ x i+x j<c*x k
  · have pos {a b : ℝ} (ha : 0≤a) (h' : near c a b) : 0<b := by
      by_contra! hb
      linarith [mul_nonpos_of_nonneg_of_nonpos (show 0≤c by linarith) hb, h'.1]
    have hi := pos (hx k) h.1.2.2
    have hj := pos (hx i) h.1.1
    have hk := pos (hx j) h.1.2.1
    simp [y,hi,hj,hk]
  · simp only [core,bit,if_neg h]
    split_ifs <;> norm_num

private lemma tight_of_close {c a b d : ℝ} (hc : 1<c) (hp : c*c≤c+1)
    (hd : 0<d) (hwin : a+b<c*d) (ha : d<c*a) (hb : d<c*b) : tight c a b d := by
  have h0 : 0<c := by linarith
  have hh := mul_lt_mul_of_pos_left hwin h0
  have hlim := mul_le_mul_of_nonneg_right hp hd.le
  have ad : a<d := by
    by_contra! h
    nlinarith [mul_le_mul_of_nonneg_left h h0.le]
  have bd : b<d := by
    by_contra! h
    nlinarith [mul_le_mul_of_nonneg_left h h0.le]
  have dd : d<c*d := by nlinarith [mul_lt_mul_of_pos_right hc hd]
  exact ⟨⟨ad.trans hb,bd.trans ha⟩,⟨bd.trans dd,hb⟩,⟨ha,ad.trans dd⟩⟩

private def combine (u v : ℝ) := u+v-u*v

private lemma pointwise {c a b d : ℝ} (hc : 1<c) (hp : c*c≤c+1) (hd : 0<d) :
    bit (a+b<c*d) ≤ core c a b d+combine (bad c a d) (bad c b d) := by
  classical
  by_cases h : a+b<c*d <;> by_cases h' : tight c a b d <;>
    by_cases u : c*a≤d <;> by_cases v : c*b≤d <;>
    simp [core,bit,bad,combine,h,h',u,v]
  exact (h' (tight_of_close hc hp hd h (lt_of_not_ge u) (lt_of_not_ge v))).elim

private def expect {n : ℕ} (w f : Fin n → ℝ) := ∑ i,w i*f i
private lemma econst {n : ℕ} {w : Fin n → ℝ} (hw : Mass w) (t : ℝ) :
    expect w (fun _ => t) = t := by simp [expect,← Finset.sum_mul,hw.2]

private lemma eadd {n : ℕ} (w f g : Fin n → ℝ) :
    expect w (fun i => f i+g i) = expect w f+expect w g := by
  simp [expect,mul_add,Finset.sum_add_distrib]

private lemma esub {n : ℕ} (w f g : Fin n → ℝ) :
    expect w (fun i => f i-g i) = expect w f-expect w g := by
  simp [expect,mul_sub,Finset.sum_sub_distrib]

private lemma eright {n : ℕ} (w f : Fin n → ℝ) (t : ℝ) :
    expect w (fun i => f i*t)=expect w f*t := by simp [expect,Finset.sum_mul,mul_assoc]
private lemma eleft {n : ℕ} (w f : Fin n → ℝ) (t : ℝ) :
    expect w (fun i => t*f i)=t*expect w f := by simpa only [mul_comm t] using eright w f t

private lemma epair {n : ℕ} {w : Fin n → ℝ} (hw : Mass w) (f : Fin n → ℝ) :
    expect w (fun i => expect w (fun j => combine (f i) (f j))) =
      2*(expect w f)-(expect w f)^2 := by
  have inner (i : Fin n) : expect w (fun j => combine (f i) (f j)) =
      f i + expect w f - f i*expect w f := by
    simp only [combine]
    rw [esub, eadd, econst hw, eleft]
  simp_rw [inner]
  rw [esub,eadd,econst hw,eright]
  ring

private lemma evar {n : ℕ} {w : Fin n → ℝ} (hw : Mass w) (f : Fin n → ℝ) :
    (expect w f)^2 ≤ expect w (fun i => (f i)^2) := by
  let t := expect w f
  have hv : 0≤expect w (fun i => (f i-t)^2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw.1 _) (sq_nonneg _)
  have expand (i : Fin n) : (f i-t)^2 = (f i)^2 - (f i*t)*2+t^2 := by ring
  simp_rw [expand] at hv
  rw [eadd,esub,econst hw,eright,eright] at hv
  dsimp [t] at hv
  nlinarith

private lemma target_order {n : ℕ} (w : Fin n → ℝ) (f : Fin n → Fin n → Fin n → ℝ) :
    avg f w = expect w (fun k => expect w (fun i => expect w (fun j => f i j k))) := by
  unfold avg expect
  simp only [Finset.mul_sum]
  calc
    _ = ∑ i, ∑ k, ∑ j, w i*w j*w k*f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring

private lemma spread_target {n : ℕ} (c : ℝ) (x w : Fin n → ℝ) :
    spread c x w = expect w (fun k => expect w (fun i => bad c (x i) (x k))) := by
  unfold spread expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- A finite law with small pair-separation probability has small one-scale error. -/
theorem score_le_beta_add_spread {n : ℕ} {c : ℝ} (hc : 1<c) (hp : c*c≤c+1)
    (x w : Fin n → ℝ) (hx : ∀ i, 0≤x i) (hw : Mass w) :
    score c x w ≤ beta c + (2*spread c x w - (spread c x w)^2) := by
  classical
  let f (i j k : Fin n) := combine (bad c (x i) (x k)) (bad c (x j) (x k))
  let q (k : Fin n) := expect w (fun i => bad c (x i) (x k))
  have splitScore : score c x w ≤ part (core c) x w + avg f w := by
    unfold score part avg
    simp_rw [← Finset.sum_add_distrib]
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
    by_cases hk : 0<x k
    swap
    · have unsucc : ¬Win c x i j k := by
        unfold Win
        have zero : x k=0 := le_antisymm (le_of_not_gt hk) (hx k)
        rw [zero,mul_zero]
        exact not_lt_of_ge (add_nonneg (hx _) (hx _))
      have cs : 0≤core c (x i) (x j) (x k) := by unfold core bit; split_ifs <;> norm_num
      have fs : 0≤f i j k := by unfold f combine bad bit; split_ifs <;> norm_num
      simpa [unsucc] using add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (hw.1 i) (hw.1 j)) (hw.1 k)) cs)
        (mul_nonneg (mul_nonneg (mul_nonneg (hw.1 i) (hw.1 j)) (hw.1 k)) fs)
    have hh := mul_le_mul_of_nonneg_left (pointwise hc hp hk (a:=x i) (b:=x j))
      (mul_nonneg (mul_nonneg (hw.1 i) (hw.1 j)) (hw.1 k))
    rw [mul_add] at hh
    by_cases h : x i+x j<c*x k <;> simpa [Win,f,bit,h] using hh
  have eval : avg f w = 2*expect w q - expect w (fun k => (q k)^2) := by
    rw [target_order]
    change expect w (fun k => expect w (fun i => expect w (fun j =>
      combine (bad c (x i) (x k)) (bad c (x j) (x k))))) = _
    simp_rw [epair hw]
    exact (esub w (fun k => 2*q k) (fun k => (q k)^2)).trans (by rw [eleft])
  rw [spread_target,show expect w (fun k => expect w (fun i => bad c (x i) (x k)))=expect w q from rfl]
  rw [eval] at splitScore
  linarith [core_nonnegative_support hc x w hx hw,evar hw q]

open MeasureTheory ProbabilityTheory Set Filter IidJumpSpectra
open scoped ENNReal NNReal Topology

private def triplePerm (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun v := (v 1,v 2,v 0)
  invFun p := ![p.2.2, p.1, p.2.1]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv p := by rfl

private lemma triple_transfer (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (F : (Fin 3 → ℝ≥0) → ℝ) (hF : Measurable F) {M B : ℝ}
    (hb : ∀ v, 0≤F v ∧ F v≤M)
    (hfin : ∀ (N : ℕ), 0<N → ∀ x : Fin N → ℝ≥0,
        (∑ q : Comparison 2 N, F (x ∘ Fin.cons q.2 q.1)) ≤ (N:ℝ)^3*B) :
    (∫ v, F v ∂(Measure.pi (fun _ : Fin 3 => μ))) ≤ B := by
  let I := ∫ v, F v ∂(Measure.pi (fun _ : Fin 3 => μ))
  have ev : ∀ᶠ N : ℕ in atTop, survival 3 N*I ≤ B := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    let ν := Measure.pi (fun _ : Fin N => μ)
    let G := goodComparisons 2 N
    let sel (q : Comparison 2 N) (x : Fin N → ℝ≥0) := x ∘ Fin.cons q.2 q.1
    have hm (q : Comparison 2 N) : Measurable (sel q) :=
      measurable_pi_lambda _ fun _ => measurable_pi_apply _
    have hi (q : Comparison 2 N) : Integrable (fun x => F (sel q x)) ν := by
      apply (integrable_const M).mono' (hF.comp (hm q)).aestronglyMeasurable
      exact Eventually.of_forall fun x => by simpa [Real.norm_eq_abs,abs_of_nonneg (hb _).1] using (hb (sel q x)).2
    have hval (q : Comparison 2 N) (hq : q∈G) : ∫ x, F (sel q x) ∂ν = I := by
      have hmap : ν.map (sel q) = Measure.pi (fun _ : Fin 3 => μ) :=
        iid_map_injection μ _ (Finset.mem_filter.mp hq).2
      dsimp only [I]
      rw [←hmap, integral_map (hm q).aemeasurable hF.aestronglyMeasurable]
    have h : (G.card:ℝ)*I ≤ (N:ℝ)^3*B := by
      calc
        _ = ∫ x, ∑ q ∈ G, F (sel q x) ∂ν := by
          rw [integral_finset_sum _ (fun q _ => hi q)]
          simp [Finset.sum_congr rfl hval]
        _ ≤ ∫ _ : Fin N → ℝ≥0, ((N:ℝ)^3*B) ∂ν := by
          apply integral_mono (integrable_finset_sum _ (fun q _ => hi q)) (integrable_const _)
          intro x
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
            (fun q _ _ => (hb (sel q x)).1)) (hfin N (by omega) x)
        _ = _ := by simp
    rw [survival,div_mul_eq_mul_div,div_le_iff₀ (pow_pos hpos _),← goodComparisons_card 2 N]
    simpa [G,mul_comm B] using h
  apply le_of_tendsto_of_tendsto _ tendsto_const_nhds ev
  simpa [I] using (survival_tendsto 3).mul (tendsto_const_nhds (x := I))

private def separated (c : ℝ) : Set (Fin 3 → ℝ≥0) := {v | c*(v 1 : ℝ)≤(v 0 : ℝ)}

private lemma meas_sep (c : ℝ) : MeasurableSet (separated c) := by
  apply measurableSet_le <;> fun_prop

/-- The probability that the first draw multiplied by c does not exceed a second independent draw. -/
def lawSpread (c : ℝ) (μ : Measure ℝ≥0) :=
  ((Measure.pi (fun _ : Fin 3 => μ)) (separated c)).toReal

private lemma tangent_sum {c t : ℝ} (hc : 1<c) (hp : c*c≤c+1) (N : ℕ)
    (hn : 0<N) (x : Fin N → ℝ≥0) :
    (∑ q : Comparison 2 N,
      ((winEvent 2 c).indicator (fun _ => (1:ℝ)) (x ∘ Fin.cons q.2 q.1) +
      (separated c)ᶜ.indicator (fun _ => 2*(1-t)) (x ∘ Fin.cons q.2 q.1))) ≤
      (N:ℝ)^3*(beta c + t^2 + 2*(1-t)) := by
  classical
  let z (i : Fin N) := (x i : ℝ)
  let w (_ : Fin N) := 1/(N:ℝ)
  let a := 2*(1-t)
  have hN : (0:ℝ)<N := by exact_mod_cast hn
  have hw : Mass w := ⟨fun _ => by dsimp [w]; positivity,by simp [w,hN.ne']⟩
  let H (i j k : Fin N) := bit (z i+z j<c*z k)+a*(1-bad c (z i) (z k))
  let eqv := (comparisonEquiv 2 N).trans (triplePerm (Fin N))
  have hsum : (∑ q : Comparison 2 N,
      ((winEvent 2 c).indicator (fun _ => (1:ℝ)) (x ∘ Fin.cons q.2 q.1) +
      (separated c)ᶜ.indicator (fun _ => 2*(1-t)) (x ∘ Fin.cons q.2 q.1))) =
      ∑ i, ∑ j, ∑ k, H i j k := by
    let funH (p : Fin N × Fin N × Fin N) := H p.1 p.2.1 p.2.2
    calc
      _ = ∑ p, funH p := by
        apply Fintype.sum_equiv eqv
        intro q
        simp [eqv,triplePerm,comparisonEquiv,Fin.consEquiv,Set.indicator_apply,funH,H,z,bit,bad,
          winEvent,separated,Fin.sum_univ_two,Function.comp_apply,a]
        by_cases h : c*(x (q.1 0) : ℝ)≤(x q.2 : ℝ)
        · simp [h,not_lt.mpr h]
        · simp [h,lt_of_not_ge h]
      _ = _ := by simp [funH,Fintype.sum_prod_type]
  have hscale : (∑ i,∑ j,∑ k,H i j k)=(N:ℝ)^3*avg H w := by
    unfold avg
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    dsimp [w]; field_simp [hN.ne']; ring
  have hweighted : avg H w = score c z w + a*(1-spread c z w) := by
    let U (i j k : Fin N) := bit (z i+z j<c*z k)
    let V (i _ k : Fin N) := (1-bad c (z i) (z k))
    have decomp : avg H w = avg U w + a*avg V w := by
      unfold avg
      simp_rw [Finset.mul_sum]
      simp_rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      dsimp [H,U,V]; ring
    rw [decomp]
    have Uscore : avg U w=score c z w := by
      unfold avg score
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      by_cases h : Win c z i j k <;> simp [U,bit,show (z i+z j<c*z k) ↔ Win c z i j k from Iff.rfl,h]
    rw [Uscore,target_order,spread_target]
    have vinner (i k : Fin N) : expect w (fun j => V i j k)=1-bad c (z i) (z k) := econst hw _
    simp_rw [vinner,esub,econst hw]
  rw [hsum,hscale,hweighted]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hN.le _)
  have hh := score_le_beta_add_spread hc hp z w (fun i => (x i).property) hw
  dsimp [a]
  nlinarith [sq_nonneg (spread c z w-t)]

/-- One-scale compression with a distribution-dependent defect for arbitrary nonnegative Borel laws. -/
theorem iidWin_le_beta_add_spread {c : ℝ} (hc : 1<c) (hp : c*c≤c+1)
    (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] :
    iidWin 2 c μ ≤ beta c + (2*lawSpread c μ - (lawSpread c μ)^2) := by
  let ν := Measure.pi (fun _ : Fin 3 => μ)
  let D := lawSpread c μ
  let a := 2*(1-D)
  let A := winEvent 2 c
  let E := separated c
  have hA : MeasurableSet A := measurableSet_winEvent 2 c
  have hE : MeasurableSet E := meas_sep c
  have hD : D≤1 := by
    change (ν E).toReal≤1
    simpa using (ENNReal.toReal_mono (measure_ne_top ν univ) (measure_mono (Set.subset_univ E) : ν E≤ν univ))
  have ha : 0≤a := by dsimp [a]; linarith
  let F := fun v => A.indicator (fun _ => (1:ℝ)) v + Eᶜ.indicator (fun _ => a) v
  have hF : Measurable F := (measurable_const.indicator hA).add (measurable_const.indicator hE.compl)
  have rangeF (v) : 0≤F v ∧ F v≤1+a := by
    dsimp [F]
    by_cases vA : v∈A <;> by_cases vE : v∈E <;> simp [vA,vE,Set.indicator_apply] <;> linarith
  have hh := triple_transfer μ F hF rangeF (fun N hN x => tangent_sum (t:=D) hc hp N hN x)
  have hin : (∫ v, F v ∂ν) = iidWin 2 c μ + a*(1-D) := by
    dsimp only [F]
    rw [integral_add ((integrable_const _).indicator hA) ((integrable_const _).indicator hE.compl),
      integral_indicator_const _ hA,integral_indicator_const _ hE.compl,measureReal_compl hE]
    change _ = (ν A).toReal+_
    simp [measureReal_def,D,a,lawSpread,ν,E,smul_eq_mul,mul_comm]
  change (∫ v,F v ∂ν) ≤ _ at hh
  rw [hin] at hh
  dsimp [a,D] at hh ⊢
  nlinarith

#print axioms score_le_beta_add_spread
#print axioms iidWin_le_beta_add_spread
end OneScale.WeightedBridge
