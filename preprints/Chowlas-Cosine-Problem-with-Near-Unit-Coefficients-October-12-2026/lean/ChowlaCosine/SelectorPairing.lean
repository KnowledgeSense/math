import ChowlaCosine.PaperAuxiliary

namespace ChowlaCosine
open MeasureTheory AddCircle
open scoped ComplexConjugate

theorem J_localVector_mem_B {A : Finset ℤ} {s : ℤ → ℝ} {t m : ℤ}
    (hs : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01) (hm : m ∈ B A t) :
    (5.27 : ℝ) ≤ J (localVector A s t m) := by
  obtain ⟨hma, hmt, hmp⟩ := Finset.mem_filter.mp hm
  rw [show (5.27 : ℝ) = 527/100 by norm_num]
  apply J_boundary_ge _ (admissible_localVector hs t m)
  · simpa [localVector, supportedCoefficient, hmt] using (show (99/100:ℝ) ≤ s (m-t) by linarith [(hs (m-t) hmt).1])
  · simpa [localVector, supportedCoefficient, hma] using (show (99/100:ℝ) ≤ s m by linarith [(hs m hma).1])
  · simp [localVector, supportedCoefficient, hmp]

theorem selector_J_sum_lower {A : Finset ℤ} {s : ℤ → ℝ} (t : ℤ)
    (hs : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01) :
    (5.27 : ℝ) * (0.99 : ℝ)^4 * (B A t).card -
      8 * ((1.01 : ℝ)^2/100)^2 * (C A t).card ≤
    ∑ m ∈ A, J (localVector A s t m) * selectorCoefficient A s t m ^ 2 := by
  have hsub : B A t ∪ C A t ⊆ A := by
    intro m hm
    rcases Finset.mem_union.mp hm with hb | hc
    · exact (Finset.mem_filter.mp hb).1
    · exact (Finset.mem_filter.mp hc).1
  have heq := Finset.sum_subset
    (f := fun m => J (localVector A s t m) * selectorCoefficient A s t m ^ 2) hsub
    (fun m hm hnot => by rw [selectorCoefficient_zero_off_BC A s t m hnot]; simp)
  rw [← heq, Finset.sum_union (selector_BC_disjoint A t)]
  have hB : (5.27 : ℝ) * (0.99 : ℝ)^4 * (B A t).card ≤
      ∑ m ∈ B A t, J (localVector A s t m) * selectorCoefficient A s t m ^ 2 := by
    calc
      _ = ∑ m ∈ B A t, (5.27 : ℝ) * (0.99 : ℝ)^4 := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m hm
        have hj := J_localVector_mem_B hs hm
        have hb := (selectorCoefficient_mem_B hs hm).1
        have hsq : (0.99 : ℝ)^4 ≤ selectorCoefficient A s t m ^ 2 := by
          nlinarith
        exact mul_le_mul hj hsq (by positivity) (by linarith)
  have hC : -(8 * ((1.01 : ℝ)^2/100)^2 * (C A t).card) ≤
      ∑ m ∈ C A t, J (localVector A s t m) * selectorCoefficient A s t m ^ 2 := by
    calc
      _ = ∑ m ∈ C A t, -(8 * ((1.01 : ℝ)^2/100)^2) := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m hm
        have hj := (abs_le.mp (abs_J_le _ (admissible_localVector hs t m))).1
        have hb := abs_selectorCoefficient_mem_C hs hm
        have hsq : selectorCoefficient A s t m ^ 2 ≤ ((1.01 : ℝ)^2/100)^2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hb
        have hm := mul_nonneg (show 0 ≤ J (localVector A s t m) + 8 by linarith)
          (sq_nonneg (selectorCoefficient A s t m))
        nlinarith
  linarith

theorem convolve_selector_eq_polynomial (A : Finset ℤ) (s : ℤ → ℝ) (t : ℤ) :
    convolve (selector A s t) (selector A s t) =
      polynomial A (fun m => selectorCoefficient A s t m ^ 2) := by
  apply eq_polynomial_of_fourierCoeff
    (continuous_convolve (continuous_selector A s t) (continuous_selector A s t))
  intro m
  rw [fourierCoeff_convolve (continuous_selector A s t) (continuous_selector A s t),
    fourierCoeff_selector]
  by_cases hm : m ∈ A
  · simp [hm, pow_two]
  · rw [selectorCoefficient_zero_outside s t hm]
    simp [hm]

theorem selector_pairing_identity {A : Finset ℤ} {s : ℤ → ℝ}
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a) (t : ℤ) :
    (∫ x, (auxiliaryPhi (realPolynomial A s) t x : ℂ) *
      conj (convolve (selector A s t) (selector A s t) x) ∂haarAddCircle) =
    -Complex.I * ((∑ m ∈ A, J (localVector A s t m) *
      selectorCoefficient A s t m ^ 2 : ℝ) : ℂ) := by
  have hr := continuous_auxiliaryR (continuous_realPolynomial A s) t
  have hp : Continuous (fun x => (auxiliaryPhi (realPolynomial A s) t x : ℂ)) :=
    Complex.continuous_ofReal.comp ((hr.sub (hr.comp continuous_neg)).div_const 2)
  have hi := hp.integrable_of_hasCompactSupport
    (μ := (haarAddCircle : Measure Circle)) (HasCompactSupport.of_compactSpace _)
  rw [convolve_selector_eq_polynomial, integral_mul_conj_polynomial hi]
  simp only [paper_auxiliaryPhi_coeff hA hs, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem selector_pairing_lower {A : Finset ℤ} {s : ℤ → ℝ} (t : ℤ)
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a)
    (hcoeff : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01) :
    (5.27 : ℝ) * (0.99 : ℝ)^4 * (B A t).card -
      8 * ((1.01 : ℝ)^2/100)^2 * (C A t).card ≤
    ‖∫ x, (auxiliaryPhi (realPolynomial A s) t x : ℂ) *
      conj (convolve (selector A s t) (selector A s t) x) ∂haarAddCircle‖ := by
  rw [selector_pairing_identity hA hs]
  simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  exact (selector_J_sum_lower t hcoeff).trans (le_abs_self _)

end ChowlaCosine
