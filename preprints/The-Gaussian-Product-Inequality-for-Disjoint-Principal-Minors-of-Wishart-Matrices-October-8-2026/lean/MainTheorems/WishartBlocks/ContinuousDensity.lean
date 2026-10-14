import MainTheorems.WishartBlocks.EigenvalueLattice
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace ResearchMain.WishartBlocks

open scoped BigOperators

theorem positive_gap_lattice (a b c d : ℝ) :
    max 0 (b - a) * max 0 (d - c) ≤
      max 0 (min b d - min a c) * max 0 (max b d - max a c) := by
  by_cases hab : a < b
  · by_cases hcd : c < d
    · have hi : min a c < min b d :=
        lt_min ((min_le_left _ _).trans_lt hab) ((min_le_right _ _).trans_lt hcd)
      have hs : max a c < max b d :=
        max_lt (hab.trans_le (le_max_left _ _)) (hcd.trans_le (le_max_right _ _))
      simpa only [max_eq_right (sub_pos.mpr hab).le, max_eq_right (sub_pos.mpr hcd).le,
        max_eq_right (sub_pos.mpr hi).le, max_eq_right (sub_pos.mpr hs).le] using
        (gap_lattice (a := a) (b := b) (c := c) (d := d))
    · rw [max_eq_left (sub_nonpos.mpr (le_of_not_gt hcd)), mul_zero]
      exact mul_nonneg (le_max_left _ _) (le_max_left _ _)
  · rw [max_eq_left (sub_nonpos.mpr (le_of_not_gt hab)), zero_mul]
    exact mul_nonneg (le_max_left _ _) (le_max_left _ _)

noncomputable def positiveGapProduct {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 < ij.2),
    max 0 (x ij.2 - x ij.1)

theorem positiveGapProduct_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ positiveGapProduct x :=
  Finset.prod_nonneg fun _ _ => le_max_left _ _

theorem positiveGapProduct_continuous (n : ℕ) :
    Continuous (positiveGapProduct (n := n)) := by
  unfold positiveGapProduct
  fun_prop

theorem positiveGapProduct_lattice {n : ℕ} (x y : Fin n → ℝ) :
    positiveGapProduct x * positiveGapProduct y ≤
      positiveGapProduct (x ⊓ y) * positiveGapProduct (x ⊔ y) := by
  unfold positiveGapProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro ij _
    exact mul_nonneg (le_max_left _ _) (le_max_left _ _)
  · intro ij _
    exact positive_gap_lattice _ _ _ _

theorem positiveGapProduct_eq_gapProduct {n : ℕ} {x : Fin n → ℝ} (hx : StrictMono x) :
    positiveGapProduct x = gapProduct x := by
  unfold positiveGapProduct gapProduct
  apply Finset.prod_congr rfl
  intro ij hij
  exact max_eq_right (sub_pos.mpr (hx (Finset.mem_filter.mp hij).2)).le

theorem positiveGapProduct_eq_zero {n : ℕ} {x : Fin n → ℝ} (hx : ¬StrictMono x) :
    positiveGapProduct x = 0 := by
  simp only [StrictMono] at hx
  push Not at hx
  obtain ⟨i, j, hij, hji⟩ := hx
  unfold positiveGapProduct
  apply Finset.prod_eq_zero (i := (i, j)) (Finset.mem_filter.mpr ⟨by simp, hij⟩)
  exact max_eq_left (sub_nonpos.mpr hji)

noncomputable def orderedWeight {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∏ i, f (x i)) * positiveGapProduct x

theorem orderedWeight_continuous {n : ℕ} {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (orderedWeight (n := n) f) := by
  unfold orderedWeight
  exact (continuous_finsetProd _ fun i _ => hf.comp (continuous_apply i)).mul
    (positiveGapProduct_continuous n)

theorem orderedWeight_nonneg {n : ℕ} {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t)
    (x : Fin n → ℝ) : 0 ≤ orderedWeight f x := by
  exact mul_nonneg (Finset.prod_nonneg fun i _ => hf (x i)) (positiveGapProduct_nonneg x)

theorem orderedWeight_lattice {n : ℕ} {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t)
    (x y : Fin n → ℝ) :
    orderedWeight f x * orderedWeight f y ≤
      orderedWeight f (x ⊓ y) * orderedWeight f (x ⊔ y) := by
  unfold orderedWeight
  calc
    ((∏ i, f (x i)) * positiveGapProduct x) * ((∏ i, f (y i)) * positiveGapProduct y)
        = ((∏ i, f (x i)) * (∏ i, f (y i))) *
          (positiveGapProduct x * positiveGapProduct y) := by ring
    _ ≤ ((∏ i, f (x i)) * (∏ i, f (y i))) *
          (positiveGapProduct (x ⊓ y) * positiveGapProduct (x ⊔ y)) :=
      mul_le_mul_of_nonneg_left (positiveGapProduct_lattice x y)
        (mul_nonneg (Finset.prod_nonneg fun i _ => hf (x i))
          (Finset.prod_nonneg fun i _ => hf (y i)))
    _ = ((∏ i, f ((x ⊓ y) i)) * positiveGapProduct (x ⊓ y)) *
          ((∏ i, f ((x ⊔ y) i)) * positiveGapProduct (x ⊔ y)) := by
      rw [single_factor_lattice f x y]
      ring

theorem orderedWeight_eq_chamberWeight {n : ℕ} (f : ℝ → ℝ) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) : orderedWeight f x = chamberWeight f x := by
  classical
  by_cases hm : StrictMono x
  · simp only [orderedWeight, positiveGapProduct_eq_gapProduct hm, chamberWeight,
      ite_eq_left (show OrderedPositive x from ⟨hx, hm⟩)]
  · have h : ¬OrderedPositive x := fun h => hm h.2
    simp only [orderedWeight, positiveGapProduct_eq_zero hm, mul_zero, chamberWeight, ite_eq_right h]

noncomputable def regularizedEigenvalueWeight (α a : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  orderedWeight (fun t => (max a t) ^ ((α - n - 1) / 2) * Real.exp (-(max a t) / 2)) x

theorem regularizedEigenvalueWeight_continuous (α : ℝ) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Continuous (regularizedEigenvalueWeight (n := n) α a) := by
  unfold regularizedEigenvalueWeight
  apply orderedWeight_continuous
  apply Continuous.mul
  · apply Continuous.rpow_const
    · fun_prop
    · intro t
      exact Or.inl ((ha.trans_le (le_max_left _ _)).ne')
  · fun_prop

theorem regularizedEigenvalueWeight_nonneg (α : ℝ) {a : ℝ} (ha : 0 < a) {n : ℕ}
    (x : Fin n → ℝ) : 0 ≤ regularizedEigenvalueWeight α a x := by
  apply orderedWeight_nonneg
  intro t
  exact mul_nonneg (Real.rpow_nonneg ((ha.trans_le (le_max_left _ _)).le) _)
    (Real.exp_pos _).le

theorem regularizedEigenvalueWeight_lattice (α : ℝ) {a : ℝ} (ha : 0 < a) {n : ℕ}
    (x y : Fin n → ℝ) :
    regularizedEigenvalueWeight α a x * regularizedEigenvalueWeight α a y ≤
      regularizedEigenvalueWeight α a (x ⊓ y) * regularizedEigenvalueWeight α a (x ⊔ y) := by
  apply orderedWeight_lattice
  intro t
  exact mul_nonneg (Real.rpow_nonneg ((ha.trans_le (le_max_left _ _)).le) _)
    (Real.exp_pos _).le

theorem regularizedEigenvalueWeight_eq (α : ℝ) {a : ℝ} (ha : 0 < a) {n : ℕ}
    {x : Fin n → ℝ} (hx : ∀ i, a ≤ x i) :
    regularizedEigenvalueWeight α a x = eigenvalueWeight α x := by
  unfold regularizedEigenvalueWeight eigenvalueWeight
  rw [orderedWeight_eq_chamberWeight _ (fun i => ha.trans_le (hx i))]
  unfold chamberWeight
  split_ifs
  · apply congrArg (fun z : ℝ => z * gapProduct x)
    apply Finset.prod_congr rfl
    intro i _
    dsimp only
    rw [max_eq_right (hx i)]
  · rfl

end ResearchMain.WishartBlocks
