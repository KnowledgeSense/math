import MainTheorems.Corona.Concentration
import MainTheorems.Corona.CoronaPolynomial
import MainTheorems.Corona.Balance

namespace ResearchMain.Corona

open Polynomial

noncomputable def leftComponent (h : ℝ[X]) (a m : ℕ) : ℝ[X] := h ^ (2 * m) * (h + X) ^ a
noncomputable def rightComponent (h : ℝ[X]) (a m : ℕ) : ℝ[X] :=
  h ^ (a + m) * (h + C 2 * X) ^ m
noncomputable def correction (h : ℝ[X]) (a m : ℕ) : ℝ[X] := h ^ (a + 2 * m)

theorem twoPeakPolynomial_components (h : ℝ[X]) (a m : ℕ) :
    twoPeakPolynomial h a m = leftComponent h a m + rightComponent h a m - correction h a m := rfl

theorem mass_add_linear (h : ℝ[X]) (t : ℝ) : mass (h + C t * X) = mass h + t := by
  simp only [mass, eval_add, eval_mul, eval_C, eval_X, mul_one]

theorem firstMoment_add_linear (h : ℝ[X]) (t : ℝ) :
    firstMoment (h + C t * X) = firstMoment h + t := by
  simp only [firstMoment, eulerDerivative, derivative_add, derivative_mul, derivative_C,
    derivative_X, zero_mul, mul_one, zero_add, eval_add, eval_mul, eval_C, eval_X, mul_one]

theorem mean_add_linear (h : ℝ[X]) (t : ℝ) (hh : mass h ≠ 0) (ht : mass h + t ≠ 0) :
    mean (h + C t * X) = mean h + t * (1 - mean h) / (mass h + t) := by
  simp only [mean, firstMoment_add_linear, mass_add_linear]
  field_simp
  ring

theorem NonnegativeCoefficients.add_linear {h : ℝ[X]} (hh : NonnegativeCoefficients h)
    {t : ℝ} (ht : 0 ≤ t) : NonnegativeCoefficients (h + C t * X) := by
  intro k
  simp only [coeff_add, coeff_C_mul, coeff_X]
  split_ifs
  · simpa only [mul_one] using add_nonneg (hh k) ht
  · simpa only [mul_zero, add_zero] using hh k

theorem degree_add_linear (h : ℝ[X]) (t : ℝ) {D : ℕ} (hD : h.natDegree ≤ D) (hD1 : 1 ≤ D) :
    (h + C t * X).natDegree ≤ D := by
  apply (natDegree_add_le h (C t * X)).trans
  apply max_le hD
  exact ((natDegree_C_mul_le t X).trans natDegree_X_le).trans hD1

theorem leftComponent_nonnegative {h : ℝ[X]} (hh : NonnegativeCoefficients h) (a m : ℕ) :
    NonnegativeCoefficients (leftComponent h a m) := by
  have ht := hh.add_linear (t := 1) (by norm_num)
  simpa only [map_one, one_mul, leftComponent] using (hh.pow (2 * m)).mul (ht.pow a)

theorem rightComponent_nonnegative {h : ℝ[X]} (hh : NonnegativeCoefficients h) (a m : ℕ) :
    NonnegativeCoefficients (rightComponent h a m) :=
  (hh.pow (a + m)).mul ((hh.add_linear (t := 2) (by norm_num)).pow m)

theorem leftComponent_mass (h : ℝ[X]) (a m : ℕ) :
    mass (leftComponent h a m) = mass h ^ (2 * m) * (mass h + 1) ^ a := by
  simp only [leftComponent, mass, eval_mul, eval_pow, eval_add, eval_X]

theorem rightComponent_mass (h : ℝ[X]) (a m : ℕ) :
    mass (rightComponent h a m) = mass h ^ (a + m) * (mass h + 2) ^ m := by
  simp only [rightComponent, mass, eval_mul, eval_pow, eval_add, eval_C, eval_X, mul_one]

theorem leftComponent_balanced_mass (h : ℝ[X]) (a m : ℕ) (hq : mass h ≠ 0) :
    mass (leftComponent h a m) = mass h ^ (a + 2 * m) * (1 + 1 / mass h) ^ a := by
  rw [leftComponent_mass]
  have he : mass h + 1 = mass h * (1 + 1 / mass h) := by field_simp
  rw [he, mul_pow]
  rw [show a + 2 * m = 2 * m + a by omega, pow_add]
  ring

theorem rightComponent_balanced_mass (h : ℝ[X]) (a m : ℕ) (hq : mass h ≠ 0) :
    mass (rightComponent h a m) = mass h ^ (a + 2 * m) * (1 + 2 / mass h) ^ m := by
  rw [rightComponent_mass]
  have he : mass h + 2 = mass h * (1 + 2 / mass h) := by field_simp
  rw [he, mul_pow]
  rw [show a + 2 * m = (a + m) + m by omega, pow_add]
  ring

theorem component_mass_balance (h : ℝ[X]) (hq : 1 ≤ mass h) (m : ℕ) :
    mass (rightComponent h (balanceIndex (mass h) m) m) / 2 ≤
        mass (leftComponent h (balanceIndex (mass h) m) m) ∧
      mass (leftComponent h (balanceIndex (mass h) m) m) ≤
        mass (rightComponent h (balanceIndex (mass h) m) m) := by
  have hq0 : 0 < mass h := by linarith
  have hb := balanceIndex_powers hq0 m
  have hu : 1 + 1 / mass h ≤ 2 := by
    have hbound : (1 : ℝ) / mass h ≤ 1 := (div_le_iff₀ hq0).mpr (by simpa only [one_mul] using hq)
    linarith
  rw [leftComponent_balanced_mass _ _ _ (ne_of_gt hq0),
    rightComponent_balanced_mass _ _ _ (ne_of_gt hq0)]
  constructor
  · have hbal := mul_lt_mul_of_pos_left hb.2 (pow_pos hq0 (balanceIndex (mass h) m + 2 * m))
    rw [pow_succ] at hbal
    have hnonneg : 0 ≤ mass h ^ (balanceIndex (mass h) m + 2 * m) *
        (1 + 1 / mass h) ^ balanceIndex (mass h) m := by positivity
    nlinarith only [hbal, hu, hnonneg]
  · exact mul_le_mul_of_nonneg_left hb.1 (pow_nonneg hq0.le _)

theorem leftComponent_mean (h : ℝ[X]) (hq : 0 < mass h) (a m : ℕ) :
    mean (leftComponent h a m) = (a + 2 * m : ℕ) * mean h +
      (1 - mean h) * a / (mass h + 1) := by
  have ht : 0 < mass (h + C 1 * X) := by rw [mass_add_linear]; linarith
  have he : h + X = h + C 1 * X := by simp
  rw [leftComponent, he, mean_mul _ _ (by rw [mass_pow]; exact pow_ne_zero _ (ne_of_gt hq))
    (by rw [mass_pow]; exact pow_ne_zero _ (ne_of_gt ht)),
    mean_pow _ (ne_of_gt hq), mean_pow _ (ne_of_gt ht),
    mean_add_linear _ _ (ne_of_gt hq) (by linarith)]
  push_cast
  ring

theorem rightComponent_mean (h : ℝ[X]) (hq : 0 < mass h) (a m : ℕ) :
    mean (rightComponent h a m) = (a + 2 * m : ℕ) * mean h +
      (1 - mean h) * (2 * m) / (mass h + 2) := by
  have ht : 0 < mass (h + C 2 * X) := by rw [mass_add_linear]; linarith
  rw [rightComponent, mean_mul _ _ (by rw [mass_pow]; exact pow_ne_zero _ (ne_of_gt hq))
    (by rw [mass_pow]; exact pow_ne_zero _ (ne_of_gt ht)),
    mean_pow _ (ne_of_gt hq), mean_pow _ (ne_of_gt ht),
    mean_add_linear _ _ (ne_of_gt hq) (by linarith)]
  push_cast
  ring

end ResearchMain.Corona
