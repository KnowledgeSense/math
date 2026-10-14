import MeanMaximumForests.PeakAnalysis.BinomialMass

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset

theorem binomial_first_sum (n : ℕ) (z : ℝ) :
    (∑ k : Fin (n + 1), (n.choose k.val : ℝ) * z ^ k.val * k.val) =
      (n : ℝ) * z * (1 + z) ^ (n - 1) := by
  have h := HasDerivAt.sum (u := univ) (fun (k : Fin (n + 1)) _ =>
    ((hasDerivAt_id z).pow k.val).const_mul (n.choose k.val : ℝ))
  have he : (∑ k : Fin (n + 1), fun x : ℝ => (n.choose k.val : ℝ) * (id x) ^ k.val) =
      fun x => (1 + x) ^ n := by
    funext x
    simp only [Finset.sum_apply, id_eq]
    exact binomialWeight_sum n x
  simp only [Pi.pow_apply] at h
  rw [he] at h
  have h' := ((hasDerivAt_id z).const_add 1).pow n
  have hd := h.unique h'
  simp only [id_eq, mul_one] at hd
  have hm := congrArg (fun x : ℝ => z * x) hd
  rw [mul_sum] at hm
  have hterms (k : Fin (n + 1)) : z * ((n.choose k.val : ℝ) * (k.val * z ^ (k.val - 1))) =
      (n.choose k.val : ℝ) * z ^ k.val * k.val := by
    by_cases hk : k.val = 0
    · simp [hk]
    · have he : z * z ^ (k.val - 1) = z ^ k.val := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      calc
        _ = (n.choose k.val : ℝ) * (z * z ^ (k.val - 1)) * k.val := by ring
        _ = _ := by rw [he]
  simp_rw [hterms] at hm
  nlinarith only [hm]

theorem binomialSizeLaw_mean (n : ℕ) (z : ℝ) (hz : 0 < z) :
    (binomialSizeLaw n z hz).expectation (fun k => (k.val : ℝ)) = n * z / (1 + z) := by
  unfold FiniteLaw.expectation binomialSizeLaw binomialSizeMass
  simp only [div_mul_eq_mul_div, ← sum_div, binomial_first_sum]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp

 theorem binomial_tiltPartition (n : ℕ) (t : ℝ) :
    tiltPartition (binomialSizeLaw n 1 (by norm_num)) (fun k => (k.val : ℝ)) t =
      (1 + Real.exp t) ^ n / 2 ^ n := by
  unfold tiltPartition tiltMoment binomialSizeLaw binomialSizeMass
  simp only [one_pow, mul_one, one_add_one_eq_two, div_mul_eq_mul_div, ← sum_div]
  congr 1
  rw [← binomialWeight_sum n (Real.exp t)]
  apply sum_congr rfl
  intro k _
  rw [mul_comm t, Real.exp_nat_mul]

theorem finiteTilt_binomial (n : ℕ) (t : ℝ) :
    finiteTilt (binomialSizeLaw n 1 (by norm_num)) (fun k => (k.val : ℝ)) t =
      binomialSizeLaw n (Real.exp t) (Real.exp_pos t) := by
  apply FiniteLaw.ext
  intro k
  change (binomialSizeMass n 1 k.val * Real.exp (t * k.val)) /
    (binomialSizeLaw n 1 (by norm_num)).expectation (fun k => Real.exp (t * k.val)) = _
  have he : (binomialSizeLaw n 1 (by norm_num)).expectation (fun k => Real.exp (t * k.val)) =
      tiltPartition (binomialSizeLaw n 1 (by norm_num)) (fun k => (k.val : ℝ)) t := by
    simp only [FiniteLaw.expectation, tiltPartition, tiltMoment, mul_one]
  rw [he, binomial_tiltPartition]
  change _ = binomialSizeMass n (Real.exp t) k.val
  unfold binomialSizeMass
  simp only [one_pow, mul_one, one_add_one_eq_two]
  rw [mul_comm t, Real.exp_nat_mul]
  field_simp

theorem binomialSizeLaw_exp_variance (n : ℕ) (t : ℝ) :
    (binomialSizeLaw n (Real.exp t) (Real.exp_pos t)).variance (fun k => (k.val : ℝ)) =
      n * Real.exp t / (1 + Real.exp t) ^ 2 := by
  have h := finiteTilt_mean_hasDerivAt (binomialSizeLaw n 1 (by norm_num))
    (fun k => (k.val : ℝ)) t
  simp_rw [finiteTilt_binomial, binomialSizeLaw_mean] at h
  have h' := ((Real.hasDerivAt_exp t).const_mul (n : ℝ)).div
    ((Real.hasDerivAt_exp t).const_add 1) (by positivity : (1 + Real.exp t) ≠ 0)
  have he := h.unique h'
  rw [he]
  field_simp
  ring

theorem binomialSizeLaw_variance (n : ℕ) (z : ℝ) (hz : 0 < z) :
    (binomialSizeLaw n z hz).variance (fun k => (k.val : ℝ)) = n * z / (1 + z) ^ 2 := by
  have h := binomialSizeLaw_exp_variance n (Real.log z)
  simpa only [Real.exp_log hz] using h

theorem binomialSizeLaw_variance_le (n : ℕ) (z : ℝ) (hz : 0 < z) :
    (binomialSizeLaw n z hz).variance (fun k => (k.val : ℝ)) ≤ (n : ℝ) / 4 := by
  rw [binomialSizeLaw_variance]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)).mpr
  have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (z - 1))
  nlinarith only [h]

end MeanMaximumForests.PeakAnalysis
