import MainTheorems.Corona.PeakParameters

namespace ResearchMain.Corona

open Polynomial

theorem leftComponent_mass_positive (h : ℝ[X]) (hq : 0 < mass h) (a m : ℕ) :
    0 < mass (leftComponent h a m) := by
  rw [leftComponent_mass]
  positivity

theorem rightComponent_mass_positive (h : ℝ[X]) (hq : 0 < mass h) (a m : ℕ) :
    0 < mass (rightComponent h a m) := by
  rw [rightComponent_mass]
  positivity

theorem leftComponent_variance {h : ℝ[X]} (hh : NonnegativeCoefficients h) (hq : 0 < mass h)
    {D : ℕ} (hD : h.natDegree ≤ D) (hD1 : 1 ≤ D) (a m : ℕ) :
    variance (leftComponent h a m) ≤ (a + 2 * m : ℕ) * (D : ℝ) ^ 2 := by
  have ht : 0 < mass (h + C 1 * X) := by rw [mass_add_linear]; linarith
  have he : h + X = h + C 1 * X := by simp
  rw [leftComponent, he, variance_mul _ _ (by rw [mass_pow]; exact pow_ne_zero _ (ne_of_gt hq))
    (by rw [mass_pow]; exact pow_ne_zero _ (ne_of_gt ht)),
    variance_pow _ (ne_of_gt hq), variance_pow _ (ne_of_gt ht)]
  have h₁ := mul_le_mul_of_nonneg_left (variance_bound hh hq hD) (show (0 : ℝ) ≤ 2 * m by positivity)
  have h₂ := mul_le_mul_of_nonneg_left
    (variance_bound (hh.add_linear (t := 1) (by norm_num)) ht (degree_add_linear h 1 hD hD1))
    (show (0 : ℝ) ≤ a by positivity)
  push_cast
  nlinarith only [h₁, h₂]

theorem rightComponent_variance {h : ℝ[X]} (hh : NonnegativeCoefficients h) (hq : 0 < mass h)
    {D : ℕ} (hD : h.natDegree ≤ D) (hD1 : 1 ≤ D) (a m : ℕ) :
    variance (rightComponent h a m) ≤ (a + 2 * m : ℕ) * (D : ℝ) ^ 2 := by
  have ht : 0 < mass (h + C 2 * X) := by rw [mass_add_linear]; linarith
  rw [rightComponent, variance_mul _ _ (by rw [mass_pow]; exact pow_ne_zero _ (ne_of_gt hq))
    (by rw [mass_pow]; exact pow_ne_zero _ (ne_of_gt ht)),
    variance_pow _ (ne_of_gt hq), variance_pow _ (ne_of_gt ht)]
  have h₁ := mul_le_mul_of_nonneg_left (variance_bound hh hq hD)
    (show (0 : ℝ) ≤ a + m by positivity)
  have h₂ := mul_le_mul_of_nonneg_left
    (variance_bound (hh.add_linear (t := 2) (by norm_num)) ht (degree_add_linear h 2 hD hD1))
    (show (0 : ℝ) ≤ m by positivity)
  push_cast at *
  nlinarith only [h₁, h₂]

theorem balanced_variance_bound {h : ℝ[X]} (hh : NonnegativeCoefficients h) (hq : 0 < mass h)
    {D : ℕ} (hD : h.natDegree ≤ D) (hD1 : 1 ≤ D) {m : ℕ} (hm : 1 ≤ m) :
    variance (leftComponent h (balanceIndex (mass h) m) m) ≤ 4 * D ^ 2 * m ∧
      variance (rightComponent h (balanceIndex (mass h) m) m) ≤ 4 * D ^ 2 * m := by
  have ha := (balanceIndex_order hq hm).2.le
  have hA := leftComponent_variance hh hq hD hD1 (balanceIndex (mass h) m) m
  have hB := rightComponent_variance hh hq hD hD1 (balanceIndex (mass h) m) m
  have hac : (balanceIndex (mass h) m : ℝ) ≤ 2 * m := by exact_mod_cast ha
  have hsq : (0 : ℝ) ≤ (D : ℝ) ^ 2 := sq_nonneg _
  push_cast at hA hB
  constructor <;> nlinarith only [hA, hB, hac, hsq]

noncomputable def separationConstant (h : ℝ[X]) : ℝ :=
  |1 - mean h| * separationRate (mass h) / 2

theorem separationConstant_positive (h : ℝ[X]) (hq : 0 < mass h) (hm : mean h ≠ 1) :
    0 < separationConstant h := by
  unfold separationConstant
  have h₁ : 0 < |1 - mean h| := abs_pos.mpr (by intro h; apply hm; linarith)
  exact div_pos (mul_pos h₁ (separationRate_positive hq)) (by norm_num)

theorem component_mean_separation (h : ℝ[X]) (hq : 0 < mass h) (m : ℕ)
    (hm : 2 / (mass h + 1) ≤ separationRate (mass h) * m) :
    separationConstant h * m ≤
      |mean (leftComponent h (balanceIndex (mass h) m) m) -
        mean (rightComponent h (balanceIndex (mass h) m) m)| := by
  have hb := balanceIndex_separation hq m
  have h₀ : 0 ≤ separationRate (mass h) * m :=
    mul_nonneg (separationRate_positive hq).le (Nat.cast_nonneg m)
  have hbracket : separationRate (mass h) * m / 2 ≤
      (balanceIndex (mass h) m : ℝ) / (mass h + 1) - 2 * m / (mass h + 2) := by
    have he : (2 : ℝ) / (mass h + 1) = 2 * (1 / (mass h + 1)) := by ring
    rw [he] at hm
    linarith
  have hnonneg : 0 ≤ (balanceIndex (mass h) m : ℝ) / (mass h + 1) - 2 * m / (mass h + 2) := by
    linarith
  rw [leftComponent_mean _ hq, rightComponent_mean _ hq]
  have he : (balanceIndex (mass h) m + 2 * m : ℕ) * mean h +
        (1 - mean h) * balanceIndex (mass h) m / (mass h + 1) -
      ((balanceIndex (mass h) m + 2 * m : ℕ) * mean h +
        (1 - mean h) * (2 * m) / (mass h + 2)) =
      (1 - mean h) * ((balanceIndex (mass h) m : ℝ) / (mass h + 1) - 2 * m / (mass h + 2)) := by ring
  rw [he, abs_mul, abs_of_nonneg hnonneg]
  unfold separationConstant
  have h := mul_le_mul_of_nonneg_left hbracket (abs_nonneg (1 - mean h))
  convert h using 1
  ring

end ResearchMain.Corona
