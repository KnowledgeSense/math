import AperyMoments.ArcsineMoments
import AperyMoments.SpectralSymmetry

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem latticeDensity_scaled {t : ℝ} (ht : t ∈ Ioo 0 1) :
    latticeDensity (4 * t) = ellipticK (1 - t ^ 2) / (2 * Real.pi ^ 2) := by
  unfold latticeDensity latticeExpression
  rw [ite_eq_left (by rw [abs_of_pos (by linarith [ht.1] : 0 < 4 * t)]; linarith [ht.2])]
  congr 2
  ring

theorem ellipticComplement_power_integrable (n : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ n * ellipticK (1 - t ^ 2)) volume 0 1 := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr ellipticComplement_integrable
  exact IntervalIntegrable.continuousOn_mul hi (by fun_prop)

theorem latticePower_scaled_integrable (n : ℕ) :
    IntervalIntegrable (fun t : ℝ => (4 * t) ^ n * latticeDensity (4 * t)) volume 0 1 := by
  have hi := IntervalIntegrable.const_mul (ellipticComplement_power_integrable n) ((4 : ℝ) ^ n / (2 * Real.pi ^ 2))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi ⊢
  apply (integrableOn_congr_fun _ measurableSet_Ioo).mp hi
  intro t ht
  dsimp only
  rw [latticeDensity_scaled ht, mul_pow]
  ring

theorem latticePower_positive_integrable (n : ℕ) :
    IntervalIntegrable (fun c : ℝ => c ^ n * latticeDensity c) volume 0 4 := by
  have h := (IntervalIntegrable.comp_mul_left_iff (f := fun c : ℝ => c ^ n * latticeDensity c)
    (a := (0 : ℝ)) (b := 4) (by norm_num : (4 : ℝ) ≠ 0)).mp
      (by simpa using latticePower_scaled_integrable n)
  exact h

theorem latticePower_neg (n : ℕ) (c : ℝ) :
    (-c) ^ n * latticeDensity (-c) = (-1 : ℝ) ^ n * (c ^ n * latticeDensity c) := by
  rw [latticeDensity_neg, neg_pow]
  ring

theorem latticePower_negative_integrable (n : ℕ) :
    IntervalIntegrable (fun c : ℝ => c ^ n * latticeDensity c) volume (-4) 0 := by
  have h : IntervalIntegrable (fun c : ℝ => (-c) ^ n * latticeDensity (-c)) volume 0 4 := by
    simp_rw [latticePower_neg]
    exact IntervalIntegrable.const_mul (latticePower_positive_integrable n) ((-1 : ℝ) ^ n)
  have hh := h.comp_sub_left 0
  simpa only [sub_zero, zero_sub, neg_neg] using hh.symm

theorem latticePower_integrable (n : ℕ) : Integrable (fun c : ℝ => c ^ n * latticeDensity c) := by
  have hi := (latticePower_negative_integrable n).trans (latticePower_positive_integrable n)
  have hset := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-4 : ℝ) ≤ 4)).mp hi
  have he : (Ioo (-4 : ℝ) 4).indicator (fun c => c ^ n * latticeDensity c) =
      (fun c => c ^ n * latticeDensity c) := by
    funext c
    by_cases hc : c ∈ Ioo (-4 : ℝ) 4
    · exact indicator_of_mem hc _
    · rw [indicator_of_notMem hc]
      have hnot : ¬|c| < 4 := by simpa only [abs_lt, mem_Ioo] using hc
      simp only [latticeDensity, ite_eq_right hnot, mul_zero]
  rw [← he]
  exact hset.integrable_indicator measurableSet_Ioo

theorem latticePower_positive_integral (n : ℕ) :
    (∫ c in (0 : ℝ)..4, c ^ n * latticeDensity c) =
      (4 ^ (n + 1) / (2 * Real.pi ^ 2)) * positiveArcsineMoment n ^ 2 := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun c : ℝ => c ^ n * latticeDensity c) 4
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  rw [← h]
  have he : (∫ t in (0 : ℝ)..1, (4 * t) ^ n * latticeDensity (4 * t)) =
      (4 ^ n / (2 * Real.pi ^ 2)) * positiveArcsineMoment n ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (4 ^ n / (2 * Real.pi ^ 2)) * (t ^ n * ellipticK (1 - t ^ 2)) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
          apply ae_iff.mpr
          simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (1 : ℝ) : volume {(1 : ℝ)} = 0)
        filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne] with t ht hne
        rw [latticeDensity_scaled ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩, mul_pow]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          integral_Ioc_eq_integral_Ioo, ellipticComplement_moment]
  rw [he, pow_succ]
  ring

theorem latticePower_integral (n : ℕ) :
    (∫ c : ℝ, c ^ n * latticeDensity c) =
      (1 + (-1 : ℝ) ^ n) * ((4 ^ (n + 1) / (2 * Real.pi ^ 2)) * positiveArcsineMoment n ^ 2) := by
  have he : (∫ c : ℝ, c ^ n * latticeDensity c) = ∫ c in (-4 : ℝ)..4, c ^ n * latticeDensity c := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-4 : ℝ) ≤ 4), integral_Ioc_eq_integral_Ioo]
    have hfun : (Ioo (-4 : ℝ) 4).indicator (fun c => c ^ n * latticeDensity c) =
        (fun c => c ^ n * latticeDensity c) := by
      funext c
      by_cases hc : c ∈ Ioo (-4 : ℝ) 4
      · exact indicator_of_mem hc _
      · rw [indicator_of_notMem hc]
        have hnot : ¬|c| < 4 := by simpa only [abs_lt, mem_Ioo] using hc
        simp only [latticeDensity, ite_eq_right hnot, mul_zero]
    conv_lhs => rw [← hfun]
    exact integral_indicator measurableSet_Ioo
  rw [he, ← intervalIntegral.integral_add_adjacent_intervals
    (latticePower_negative_integrable n) (latticePower_positive_integrable n)]
  have hn := intervalIntegral.integral_comp_neg (fun c : ℝ => c ^ n * latticeDensity c)
    (a := (0 : ℝ)) (b := 4)
  simp only [neg_zero] at hn
  simp_rw [latticePower_neg] at hn
  rw [intervalIntegral.integral_const_mul] at hn
  rw [← hn, latticePower_positive_integral]
  ring

theorem latticeMoment_even (n : ℕ) :
    (∫ c : ℝ, c ^ (2 * n) * latticeDensity c) = (n.centralBinom : ℝ) ^ 2 := by
  rw [latticePower_integral, positiveArcsineMoment_even]
  simp only [pow_mul, neg_one_sq, one_pow, one_add_one_eq_two]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [pow_succ, pow_mul]
  field_simp
  have he : (4 : ℝ) ^ (n * 2) = 16 ^ n := by rw [Nat.mul_comm, pow_mul]; norm_num
  ring_nf
  rw [he]

theorem latticeMoment_odd (n : ℕ) :
    (∫ c : ℝ, c ^ (2 * n + 1) * latticeDensity c) = 0 := by
  rw [latticePower_integral]
  simp [pow_add, pow_mul]

theorem latticeDensity_integrable : Integrable latticeDensity := by
  simpa only [pow_zero, one_mul] using latticePower_integrable 0

theorem latticeDensity_integral : (∫ c : ℝ, latticeDensity c) = 1 := by
  simpa using latticeMoment_even 0

end AperyMoments
