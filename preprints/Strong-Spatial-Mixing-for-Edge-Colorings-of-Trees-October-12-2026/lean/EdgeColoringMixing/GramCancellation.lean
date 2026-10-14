import EdgeColoringMixing.PosteriorMoments
import EdgeColoringMixing.ColumnBlocks
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset

variable {d q : ℕ}

noncomputable def normalizedCovarianceProduct (μ : FiniteLaw (Injection d q))
    (c : Fin q) (i j l : Fin d) (b : Fin q) : ℝ :=
  covariance μ (i,c) (l,b) * covariance μ (j,c) (l,b) / mean μ l b

/-- All cross-color, cross-row contributions form a Gram matrix. -/
noncomputable def crossRowGram (μ : FiniteLaw (Injection d q)) (c : Fin q) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ l, ∑ b, if b ≠ c ∧ l ≠ i ∧ l ≠ j then
    normalizedCovarianceProduct μ c i j l b else 0

private theorem same_color_product (μ : FiniteLaw (Injection d q))
    (c : Fin q) (i j l : Fin d) (hij : i ≠ j) :
    normalizedCovarianceProduct μ c i j l c =
      mean μ i c * mean μ j c * mean μ l c -
        (if l = i then mean μ i c * mean μ j c else 0) -
        (if l = j then mean μ i c * mean μ j c else 0) := by
  by_cases hli : l = i
  · subst l
    rw [normalizedCovarianceProduct, covariance_diagonal,
      covariance_same_color μ (Ne.symm hij)]
    simp only [ite_true, hij, ite_false, sub_zero]
    by_cases hp : mean μ i c = 0
    · simp [hp]
    · field_simp; ring
  · by_cases hlj : l = j
    · subst l
      rw [normalizedCovarianceProduct, covariance_diagonal, covariance_same_color μ hij]
      simp only [ite_true, hli, ite_false, sub_zero]
      by_cases hp : mean μ j c = 0
      · simp [hp]
      · field_simp; ring
    · rw [normalizedCovarianceProduct, covariance_same_color μ (Ne.symm hli),
        covariance_same_color μ (Ne.symm hlj)]
      simp only [hli, hlj, ite_false, sub_zero]
      by_cases hp : mean μ l c = 0
      · simp [hp]
      · field_simp

theorem same_color_Q_off_diagonal (μ : FiniteLaw (Injection d q))
    (c : Fin q) (i j : Fin d) (hij : i ≠ j) :
    ∑ l, normalizedCovarianceProduct μ c i j l c =
      -(2 - colorMean μ c) * mean μ i c * mean μ j c := by
  simp_rw [same_color_product μ c i j _ hij]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.mul_sum, colorMean]
  ring

private theorem first_row_product (μ : FiniteLaw (Injection d q))
    (c b : Fin q) (i j : Fin d) (hbc : b ≠ c) :
    normalizedCovarianceProduct μ c i j i b = -mean μ i c * covariance μ (j,c) (i,b) := by
  rw [normalizedCovarianceProduct, covariance_same_row μ i (Ne.symm hbc)]
  by_cases hp : mean μ i b = 0
  · rw [covariance_eq_zero_of_mean_zero μ (j,c) (i,b) hp]
    ring
  · field_simp

private theorem second_row_product (μ : FiniteLaw (Injection d q))
    (c b : Fin q) (i j : Fin d) (hbc : b ≠ c) :
    normalizedCovarianceProduct μ c i j j b = -mean μ j c * covariance μ (i,c) (j,b) := by
  rw [normalizedCovarianceProduct, covariance_same_row μ j (Ne.symm hbc)]
  by_cases hp : mean μ j b = 0
  · rw [covariance_eq_zero_of_mean_zero μ (i,c) (j,b) hp]
    ring
  · field_simp

private theorem sum_excluding {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (a : α) :
    (∑ b, if b ≠ a then f b else 0) = (∑ b, f b) - f a := by
  calc
    _ = (∑ b, f b) - ∑ b, if b = a then f b else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : b = a <;> simp [h]
    _ = _ := by simp

private theorem first_row_Q_off_color (μ : FiniteLaw (Injection d q))
    (c : Fin q) (i j : Fin d) (hij : i ≠ j) :
    (∑ b, if b ≠ c then normalizedCovarianceProduct μ c i j i b else 0) =
      -(mean μ i c)^2 * mean μ j c := by
  have hterm (b : Fin q) :
      (if b ≠ c then normalizedCovarianceProduct μ c i j i b else 0) =
      -mean μ i c * (if b ≠ c then covariance μ (j,c) (i,b) else 0) := by
    by_cases hbc : b ≠ c
    · rw [ite_eq_left hbc, ite_eq_left hbc, first_row_product μ c b i j hbc]
    · simp [hbc]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_excluding, covariance_row_sum,
    covariance_same_color μ (Ne.symm hij)]
  ring

private theorem second_row_Q_off_color (μ : FiniteLaw (Injection d q))
    (c : Fin q) (i j : Fin d) (hij : i ≠ j) :
    (∑ b, if b ≠ c then normalizedCovarianceProduct μ c i j j b else 0) =
      -mean μ i c * (mean μ j c)^2 := by
  have hterm (b : Fin q) :
      (if b ≠ c then normalizedCovarianceProduct μ c i j j b else 0) =
      -mean μ j c * (if b ≠ c then covariance μ (i,c) (j,b) else 0) := by
    by_cases hbc : b ≠ c
    · rw [ite_eq_left hbc, ite_eq_left hbc, second_row_product μ c b i j hbc]
    · simp [hbc]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_excluding, covariance_row_sum,
    covariance_same_color μ hij]
  ring

/-- The exact off-diagonal decomposition used in Gram cancellation. -/
theorem Q_off_diagonal (μ : FiniteLaw (Injection d q))
    (c : Fin q) (i j : Fin d) (hij : i ≠ j) :
    (∑ l, ∑ b, normalizedCovarianceProduct μ c i j l b) =
      -(2 - colorMean μ c) * mean μ i c * mean μ j c -
        (mean μ i c)^2 * mean μ j c - mean μ i c * (mean μ j c)^2 +
        crossRowGram μ c i j := by
  have hterm (l : Fin d) (b : Fin q) : normalizedCovarianceProduct μ c i j l b =
      (if b = c then normalizedCovarianceProduct μ c i j l b else 0) +
      (if l = i then (if b ≠ c then normalizedCovarianceProduct μ c i j l b else 0)
        else 0) +
      (if l = j then (if b ≠ c then normalizedCovarianceProduct μ c i j l b else 0)
        else 0) +
      (if b ≠ c ∧ l ≠ i ∧ l ≠ j then normalizedCovarianceProduct μ c i j l b else 0) := by
    by_cases hbc : b = c <;> by_cases hli : l = i <;> by_cases hlj : l = j
    all_goals simp_all
  calc
    _ = (∑ l, normalizedCovarianceProduct μ c i j l c) +
        (∑ b, if b ≠ c then normalizedCovarianceProduct μ c i j i b else 0) +
        (∑ b, if b ≠ c then normalizedCovarianceProduct μ c i j j b else 0) +
        crossRowGram μ c i j := by
      conv_lhs =>
        arg 2
        ext l
        arg 2
        ext b
        rw [hterm]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero, crossRowGram]
    _ = _ := by
      rw [same_color_Q_off_diagonal μ c i j hij, first_row_Q_off_color μ c i j hij,
        second_row_Q_off_color μ c i j hij]
      ring

/-- The cross-row term is a genuine positive semidefinite Gram matrix. -/
theorem crossRowGram_posSemidef (μ : FiniteLaw (Injection d q)) (c : Fin q) :
    (crossRowGram μ c).PosSemidef := by
  let v : Fin d → Fin q → Fin d → ℝ := fun l b i =>
    if b ≠ c ∧ l ≠ i then covariance μ (i,c) (l,b) else 0
  have hrepr : crossRowGram μ c =
      ∑ l, ∑ b, (mean μ l b)⁻¹ • Matrix.vecMulVec (v l b) (v l b) := by
    ext i j
    simp only [crossRowGram, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hbc : b = c <;> by_cases hli : l = i <;> by_cases hlj : l = j
    all_goals simp [v, hbc, hli, hlj, normalizedCovarianceProduct,
      div_eq_mul_inv, mul_comm]
  rw [hrepr]
  apply Matrix.posSemidef_sum
  intro l _
  apply Matrix.posSemidef_sum
  intro b _
  have h := Matrix.posSemidef_vecMulVec_self_star (v l b)
  exact (by simpa using h : (Matrix.vecMulVec (v l b) (v l b)).PosSemidef).smul
    (inv_nonneg.mpr (mean_nonneg μ l b))

/-- The unscaled retained negative block diag(p²) - p pᵀ. -/
noncomputable def negativeBlock (μ : FiniteLaw (Injection d q)) (c : Fin q) :
    Matrix (Fin d) (Fin d) ℝ := fun i j => if i = j then 0 else -mean μ i c * mean μ j c

noncomputable def posteriorGram (μ : FiniteLaw (Injection d q)) (c : Fin q) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ l, ∑ b, normalizedCovarianceProduct μ c i j l b

private theorem negative_square_off_diagonal (μ : FiniteLaw (Injection d q))
    (c : Fin q) (i j : Fin d) (hij : i ≠ j) :
    (∑ l, negativeBlock μ c i l * negativeBlock μ c l j / mean μ l c) =
      (colorMean μ c - mean μ i c - mean μ j c) * mean μ i c * mean μ j c := by
  have hterm (l : Fin d) : negativeBlock μ c i l * negativeBlock μ c l j / mean μ l c =
      mean μ i c * mean μ j c * mean μ l c -
      (if l = i then (mean μ i c)^2 * mean μ j c else 0) -
      (if l = j then mean μ i c * (mean μ j c)^2 else 0) := by
    by_cases hli : l = i
    · subst l
      simp [negativeBlock, hij]
      ring
    · by_cases hlj : l = j
      · subst l
        simp [negativeBlock, hij, Ne.symm hij]
        ring
      · simp only [negativeBlock, Ne.symm hli, hlj, hli, ite_false, sub_zero]
        by_cases hp : mean μ l c = 0
        · simp [hp]
        · field_simp
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.mul_sum, colorMean]
  ring

private theorem negative_square_diagonal (μ : FiniteLaw (Injection d q))
    (c : Fin q) (i : Fin d) :
    (∑ l, negativeBlock μ c i l * negativeBlock μ c l i / mean μ l c) =
      (mean μ i c)^2 * (colorMean μ c - mean μ i c) := by
  have hterm (l : Fin d) : negativeBlock μ c i l * negativeBlock μ c l i / mean μ l c =
      (mean μ i c)^2 * mean μ l c - (if l = i then (mean μ i c)^3 else 0) := by
    by_cases hli : l = i
    · subst l
      simp [negativeBlock]
      ring
    · simp only [negativeBlock, hli, Ne.symm hli, ite_false, sub_zero]
      by_cases hp : mean μ l c = 0
      · simp [hp]
      · field_simp
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.mul_sum, colorMean]
  ring

/-- The Gram cancellation is exact; the remaining off-diagonal term is the negative Gram block. -/
theorem gram_cancellation (μ : FiniteLaw (Injection d q)) (c : Fin q) (i j : Fin d) :
    2 * negativeBlock μ c i j +
      (if i = j then posteriorGram μ c i i else 0) - posteriorGram μ c i j +
      (∑ l, negativeBlock μ c i l * negativeBlock μ c l j / mean μ l c) =
    (if i = j then (mean μ i c)^2 * (colorMean μ c - mean μ i c) else 0) +
      (if i = j then crossRowGram μ c i i else 0) - crossRowGram μ c i j := by
  by_cases hij : i = j
  · subst j
    rw [negative_square_diagonal]
    simp [negativeBlock]
  · rw [negative_square_off_diagonal μ c i j hij]
    simp only [hij, ite_false, zero_add]
    rw [posteriorGram, Q_off_diagonal μ c i j hij]
    simp only [negativeBlock, hij, ite_false]
    ring

private theorem posteriorGram_eq_active (μ : FiniteLaw (Injection d q))
    (c : Fin q) (i j : Fin d) :
    posteriorGram μ c i j = ∑ x ∈ active μ,
      covariance μ (i,c) x * covariance μ (j,c) x / mean μ x.1 x.2 := by
  let f : Fin d × Fin q → ℝ := fun x =>
    covariance μ (i,c) x * covariance μ (j,c) x / mean μ x.1 x.2
  change (∑ l, ∑ b, f (l,b)) = ∑ x ∈ active μ, f x
  rw [← Fintype.sum_prod_type]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  dsimp only [f]
  rw [mean_eq_zero_of_not_active μ hx, div_zero]

/-- The same retained negative block in the actual law conditioned on the selected cell. -/
noncomputable def posteriorNegativeBlock (μ : FiniteLaw (Injection d q))
    (x : Fin d × Fin q) (c : Fin q) (i j : Fin d) : ℝ :=
  if i = j then 0 else -posteriorMean μ x (i,c) * posteriorMean μ x (j,c)

private theorem posteriorNegativeBlock_moment (μ : FiniteLaw (Injection d q))
    (c : Fin q) (i j : Fin d) :
    (∑ x ∈ active μ, mean μ x.1 x.2 * posteriorNegativeBlock μ x c i j) =
      (d : ℝ) * negativeBlock μ c i j +
      (if i = j then posteriorGram μ c i i else 0) - posteriorGram μ c i j := by
  by_cases hij : i = j
  · subst j
    simp [posteriorNegativeBlock, negativeBlock]
  · have hsum := posterior_second_moment μ (i,c) (j,c) rfl
    simp only [Prod.mk.injEq, hij, false_and, ite_false, sub_zero] at hsum
    rw [← posteriorGram_eq_active μ c i j] at hsum
    simp only [posteriorNegativeBlock, hij, ite_false, negativeBlock]
    calc
      _ = -(∑ x ∈ active μ,
          mean μ x.1 x.2 * posteriorMean μ x (i,c) * posteriorMean μ x (j,c)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [hsum]; ring

/-- Lemma 4.6 after multiplication by the number of remaining rows.
Every posterior term comes from the actual conditional finite injection law. -/
theorem recursive_gram_cancellation (μ : FiniteLaw (Injection d q))
    (c : Fin q) (i j : Fin d) :
    (∑ x ∈ active μ, mean μ x.1 x.2 * posteriorNegativeBlock μ x c i j) -
      ((d : ℝ) - 2) * negativeBlock μ c i j +
      (∑ l, negativeBlock μ c i l * negativeBlock μ c l j / mean μ l c) =
    (if i = j then (mean μ i c)^2 * (colorMean μ c - mean μ i c) else 0) +
      (if i = j then crossRowGram μ c i i else 0) - crossRowGram μ c i j := by
  rw [posteriorNegativeBlock_moment]
  have h := gram_cancellation μ c i j
  linear_combination h

end EdgeColoringMixing.WeightedInjection
