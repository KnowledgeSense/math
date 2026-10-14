import MainTheorems.AHOConstants.CounterexampleMatrices

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem coordinateVector_pairing (u : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i, u i * coordinateVector j i) = u j := by simp [coordinateVector]

theorem counterexample_denominator (ε z : ℝ) :
    (Matrix.trace (counterexampleA ε z * counterexampleB ε)).re =
      ε ^ 2 * smallEigenvector z 0 ^ 2 + ε * smallEigenvector z 2 ^ 2 +
      ε * largeEigenvector z 0 ^ 2 + largeEigenvector z 2 ^ 2 := by
  unfold counterexampleA counterexampleB
  simp only [mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_add, Matrix.trace_smul, realProjection_product_trace,
    coordinateVector_pairing, Complex.add_re, RCLike.real_smul_eq_coe_mul,
    RCLike.ofReal_eq_complex_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem coordinate_square_le_one {u : Fin 3 → ℝ} (hu : (∑ i, u i ^ 2) = 1)
    (j : Fin 3) : u j ^ 2 ≤ 1 := by
  rw [← hu]
  exact Finset.single_le_sum (fun i hi => sq_nonneg (u i)) (Finset.mem_univ j)

theorem largeEigenvector_third_square (z : ℝ) : largeEigenvector z 2 ^ 2 ≤ 2 * z ^ 2 := by
  have hd : 0 < 1 + z ^ 2 := rotation_denominator_positive z
  have hd₂ : 1 ≤ (1 + z ^ 2) ^ 2 := by nlinarith [sq_nonneg z]
  have hs : rotationSin z ^ 2 ≤ 4 * z ^ 2 := by
    unfold rotationSin
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd₂ (by positivity : 0 ≤ 4 * z ^ 2)]
  have he : (rotationSin z / Real.sqrt 2) ^ 2 * 2 = rotationSin z ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  change (rotationSin z / Real.sqrt 2) ^ 2 ≤ 2 * z ^ 2
  nlinarith

theorem counterexample_denominator_upper {ε z : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hεz : ε ≤ z ^ 2) :
    (Matrix.trace (counterexampleA ε z * counterexampleB ε)).re ≤ 5 * z ^ 2 := by
  rw [counterexample_denominator]
  have hv₀ := coordinate_square_le_one (smallEigenvector_norm z) 0
  have hv₂ := coordinate_square_le_one (smallEigenvector_norm z) 2
  have hu₀ := coordinate_square_le_one (largeEigenvector_norm z) 0
  have hu₂ := largeEigenvector_third_square z
  have h₁ := mul_le_mul_of_nonneg_left hv₀ (sq_nonneg ε)
  have h₂ := mul_le_mul_of_nonneg_left hv₂ hε₀
  have h₃ := mul_le_mul_of_nonneg_left hu₀ hε₀
  nlinarith

theorem counterexample_denominator_positive {ε z : ℝ} (hε : 0 < ε)
    (hz : 0 < z) (hz' : z ≤ 1 / 8) :
    0 < (Matrix.trace (counterexampleA ε z * counterexampleB ε)).re := by
  rw [counterexample_denominator]
  have hv := (active_overlaps_positive hz hz').1
  have hfirst : 0 < ε ^ 2 * smallEigenvector z 0 ^ 2 :=
    mul_pos (sq_pos_of_pos hε) (sq_pos_of_pos (by linarith))
  have hsecond : 0 ≤ ε * smallEigenvector z 2 ^ 2 := mul_nonneg hε.le (sq_nonneg _)
  have hthird : 0 ≤ ε * largeEigenvector z 0 ^ 2 := mul_nonneg hε.le (sq_nonneg _)
  nlinarith [sq_nonneg (largeEigenvector z 2)]

end ResearchMain.AHOConstants
