import OneScaleModel
import Mathlib.Topology.Order.Compact

open Finset Set
open scoped BigOperators
noncomputable section

namespace OneScale

def push {α γ : Type*} [Fintype α] [DecidableEq γ] (e : α → γ) (w : α → ℝ) (j : γ) : ℝ :=
  ∑ i, if e i = j then w i else 0

private theorem sum_push {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq γ]
    (e : α → γ) (w : α → ℝ) (g : γ → ℝ) :
    (∑ b, push e w b * g b) = ∑ i, w i*g (e i) := by
  classical
  simp only [push, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

theorem mass_push {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq γ]
    (e : α → γ) {w : α → ℝ} (hw : Mass w) : Mass (push e w) := by
  constructor
  · intro b
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hw.1])
  · simpa using (sum_push e w (fun _ => 1)).trans (by simpa using hw.2)

private def kernel {α : Type*} (c : ℝ) (x : α → ℝ) (i j k : α) : ℝ := by
  classical exact if Win c x i j k then 1 else 0

private theorem score_nested {α : Type*} [Fintype α] (c : ℝ) (x w : α → ℝ) :
    score c x w = ∑ i, w i * ∑ j, w j * ∑ k, w k * kernel c x i j k := by
  classical
  unfold score
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  by_cases h : Win c x i j k <;> simp [kernel,h,mul_assoc]

theorem score_push {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq γ]
    (e : α → γ) (c : ℝ) (z : γ → ℝ) (w : α → ℝ) :
    score c z (push e w) = score c (z ∘ e) w := by
  rw [score_nested,score_nested]
  simp_rw [sum_push e w]
  rfl

theorem score_mono_wins {α : Type*} [Fintype α] {c d : ℝ} {x y w : α → ℝ}
    (hw : Mass w) (h : ∀ i j k, Win c x i j k → Win d y i j k) :
    score c x w ≤ score d y w := by
  classical
  unfold score
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    Finset.sum_le_sum fun k _ => ?_
  by_cases a : Win c x i j k
  · simp [a,h i j k a]
  · by_cases b : Win d y i j k <;> simp [a,b, mul_nonneg, hw.1]

theorem score_le_one {α : Type*} [Fintype α] (c : ℝ) (x : α → ℝ) {w : α → ℝ}
    (hw : Mass w) : score c x w ≤ 1 := by
  classical
  unfold score
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, w i*w j*w k :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => by split_ifs <;> simp [mul_nonneg,hw.1]
    _ = 1 := by
      simp_rw [← Finset.mul_sum,hw.2,mul_one]
      simp_rw [← Finset.mul_sum,hw.2,mul_one]
      exact hw.2

theorem bdd_values (c : ℝ) : BddAbove (values c) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n,x,w,_,hw,rfl⟩
  exact score_le_one c x hw

theorem values_mono {c d : ℝ} (h : c ≤ d) {b : ℝ} (hb : b ∈ values c) :
    ∃ z ∈ values d, b ≤ z := by
  rcases hb with ⟨n,x,w,hx,hw,rfl⟩
  refine ⟨_,⟨n,x,w,fun i => ⟨(hx i).1, (hx i).2.trans_le h⟩,hw,rfl⟩,score_mono_wins hw ?_⟩
  intro i j k hg
  exact hg.trans_le (mul_le_mul_of_nonneg_right h (by linarith [(hx k).1]))

theorem values_nonempty {c : ℝ} (hc : 1 < c) : (values c).Nonempty := by
  let u : Fin 1 → ℝ := fun _ => 1
  exact ⟨_,1,u,u,fun _ => ⟨le_rfl,hc⟩,⟨fun _ => zero_le_one,by simp [u]⟩,rfl⟩

theorem beta_mono {c d : ℝ} (hc : 1 < c) (hcd : c ≤ d) : beta c ≤ beta d := by
  apply csSup_le (values_nonempty hc)
  intro b hb
  obtain ⟨z,hz,hbz⟩ := values_mono hcd hb
  exact hbz.trans (le_csSup (bdd_values d) hz)

/-- A bounded number of labels suffices to retain every winning comparison. -/
def Compressible (B : ℕ) (c : ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ), Cfg c x → ∃ (z : Fin B → ℝ) (e : Fin n → Fin B),
    Cfg c z ∧ ∀ i j k, Win c x i j k → Win c z (e i) (e j) (e k)

private abbrev Pattern (B : ℕ) := Fin B → Fin B → Fin B → Bool

private def shape {B : ℕ} (c : ℝ) (z : Fin B → ℝ) : Pattern B := fun i j k =>
  decide (z i + z j < c * z k)

private def poly {B : ℕ} (p : Pattern B) (w : Fin B → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if p i j k then w i * w j * w k else 0

private theorem poly_shape {B : ℕ} (c : ℝ) (z w : Fin B → ℝ) :
    poly (shape c z) w = score c z w := by
  classical simp [poly, shape, score,Win]

private theorem poly_continuous {B : ℕ} (p : Pattern B) : Continuous (poly p) := by
  unfold poly
  apply continuous_finset_sum; intro i _
  apply continuous_finset_sum; intro j _
  apply continuous_finset_sum; intro k _
  split_ifs <;> fun_prop

private def peak {B : ℕ} (p : Pattern B) : ℝ := sSup (poly p '' stdSimplex ℝ (Fin B))

private theorem peak_attained {B : ℕ} (hB : 0 < B) (p : Pattern B) :
    ∃ w : Fin B → ℝ, Mass w ∧ poly p w = peak p ∧
      ∀ u : Fin B → ℝ, Mass u → poly p u ≤ peak p := by
  classical
  let j : Fin B := ⟨0,hB⟩
  have hne : (stdSimplex ℝ (Fin B)).Nonempty := ⟨_,single_mem_stdSimplex ℝ j⟩
  obtain ⟨w,hw,hmax⟩ := (isCompact_stdSimplex (Fin B)).exists_isMaxOn hne (poly_continuous p).continuousOn
  have hval : IsGreatest (poly p '' stdSimplex ℝ (Fin B)) (poly p w) :=
    ⟨⟨w,hw,rfl⟩, by rintro _ ⟨u,hu,rfl⟩; exact hmax hu⟩
  have he : peak p = poly p w := hval.csSup_eq
  rw [he]
  exact ⟨w,hw,rfl,fun u hu => hmax hu⟩

def menu (B : ℕ) : Finset ℝ := by classical exact Finset.univ.image (@peak B)

theorem beta_attained_menu {B : ℕ} {c : ℝ} (hc : 1 < c) (hB : 0 < B)
    (hcompress : Compressible B c) :
    beta c ∈ menu B ∧ beta c ∈ values c := by
  classical
  let shapes : Finset (Pattern B) := Finset.univ.filter (fun p =>
    ∃ z : Fin B → ℝ, Cfg c z ∧ shape c z = p)
  have hshape (z : Fin B → ℝ) (hz : Cfg c z) : shape c z ∈ shapes :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, z,hz,rfl⟩
  have hne : shapes.Nonempty := ⟨_,hshape (fun _ => 1) (fun _ => ⟨le_rfl,hc⟩)⟩
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image shapes peak hne
  obtain ⟨z,hz,hz'⟩ := (Finset.mem_filter.mp hp).2
  obtain ⟨w,hw,hpw,_⟩ := peak_attained hB p
  have mv : peak p ∈ values c := ⟨B,z,w,hz,hw,by rw [←poly_shape,hz',hpw]⟩
  have hav : beta c ≤ peak p := by
    apply csSup_le (values_nonempty hc)
    rintro b ⟨n,x,u,hx,hu,rfl⟩
    obtain ⟨y,e,hy,hwin⟩ := hcompress n x hx
    obtain ⟨_,_,_,hb⟩ := peak_attained hB (shape c y)
    calc
      _ ≤ score c (y ∘ e) u := score_mono_wins hu hwin
      _ = score c y (push e u) := (score_push e c y u).symm
      _ = poly (shape c y) (push e u) := (poly_shape _ _ _).symm
      _ ≤ peak (shape c y) := hb _ (mass_push e hu)
      _ ≤ peak p := hmax _ (hshape y hy)
  have eqv := le_antisymm hav (le_csSup (bdd_values c) mv)
  rw [eqv]
  exact ⟨Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩,mv⟩

end OneScale
