import MainTheorems.EulerianPencil.ComplexRoots

namespace ResearchMain.EulerianPencil

open Polynomial

noncomputable def U (f : ℝ[X]) : ℝ[X] := f + X * derivative f

noncomputable def T (f : ℝ[X]) : ℝ[X] :=
  (1 + C 6 * X) * f + X * (1 + C 4 * X) * derivative f

theorem complex_eval_U (f : ℝ[X]) (z : ℂ) :
    (complexify (U f)).eval z = (complexify f).eval z + z * (complexify f).derivative.eval z := by
  simp [complexify, U]

theorem complex_eval_T (f : ℝ[X]) (z : ℂ) :
    (complexify (T f)).eval z = (1 + 6 * z) * (complexify f).eval z +
      z * (1 + 4 * z) * (complexify f).derivative.eval z := by
  simp [complexify, T, map_ofNat]

theorem splits_of_nonreal_eval_ne_zero (f : ℝ[X])
    (h : ∀ z : ℂ, z.im ≠ 0 → (complexify f).eval z ≠ 0) : f.Splits := by
  by_cases hf : f = 0
  · simp [hf]
  · apply (splits_iff_complex_roots_real hf).mpr
    intro z hz
    by_contra hi
    exact h z hi hz

theorem U_preserves_splits {f : ℝ[X]} (hs : f.Splits) : (U f).Splits := by
  by_cases hf : f = 0
  · simp [U, hf]
  · apply splits_of_nonreal_eval_ne_zero
    intro z hz he
    have hv := complex_eval_ne_zero hs hf hz
    have hz0 : z ≠ 0 := by intro h; exact hz (by simp [h])
    rw [complex_eval_U] at he
    have hl : (1 : ℂ) / z + (complexify f).derivative.eval z / (complexify f).eval z = 0 := by
      field_simp
      linear_combination he
    have hi := congrArg Complex.im hl
    simp only [Complex.add_im, one_div, Complex.inv_im, Complex.zero_im] at hi
    rw [logarithmic_derivative_im hs hf hz] at hi
    have hp : 0 < 1 / Complex.normSq z +
        (f.roots.map (fun (a : ℝ) => 1 / Complex.normSq (z - a))).sum :=
      add_pos_of_pos_of_nonneg (one_div_pos.mpr (Complex.normSq_pos.mpr hz0))
        (norm_inverse_sum_nonnegative _ _)
    apply mul_ne_zero (neg_ne_zero.mpr hz) hp.ne'
    calc
      -z.im * (1 / Complex.normSq z +
          (f.roots.map (fun (a : ℝ) => 1 / Complex.normSq (z - a))).sum) =
          -z.im / Complex.normSq z +
            -z.im * (f.roots.map (fun (a : ℝ) => 1 / Complex.normSq (z - a))).sum := by ring
      _ = 0 := hi

theorem linear_inverse_im (z : ℂ) :
    ((2 : ℂ) / (1 + 4 * z)).im = -8 * z.im / Complex.normSq (1 + 4 * z) := by
  rw [div_eq_mul_inv]
  simp [Complex.mul_im, Complex.inv_im]
  ring

theorem T_preserves_splits {f : ℝ[X]} (hs : f.Splits) : (T f).Splits := by
  by_cases hf : f = 0
  · simp [T, hf]
  · apply splits_of_nonreal_eval_ne_zero
    intro z hz he
    have hv := complex_eval_ne_zero hs hf hz
    have hz0 : z ≠ 0 := by intro h; exact hz (by simp [h])
    have hz4 : 1 + 4 * z ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      norm_num [Complex.mul_im] at hi
      exact hz (by linarith)
    rw [complex_eval_T] at he
    have hl : (1 : ℂ) / z + 2 / (1 + 4 * z) +
        (complexify f).derivative.eval z / (complexify f).eval z = 0 := by
      rw [div_add_div _ _ hz0 hz4, div_add_div _ _ (mul_ne_zero hz0 hz4) hv]
      apply div_eq_zero_iff.mpr ∘ Or.inl
      linear_combination he
    have hi := congrArg Complex.im hl
    simp only [Complex.add_im, Complex.zero_im] at hi
    rw [linear_inverse_im, logarithmic_derivative_im hs hf hz] at hi
    rw [one_div, Complex.inv_im] at hi
    have hp : 0 < 1 / Complex.normSq z + 8 / Complex.normSq (1 + 4 * z) +
        (f.roots.map (fun (a : ℝ) => 1 / Complex.normSq (z - a))).sum :=
      add_pos_of_pos_of_nonneg
        (add_pos (one_div_pos.mpr (Complex.normSq_pos.mpr hz0))
          (div_pos (by norm_num) (Complex.normSq_pos.mpr hz4)))
        (norm_inverse_sum_nonnegative _ _)
    apply mul_ne_zero (neg_ne_zero.mpr hz) hp.ne'
    calc
      -z.im * (1 / Complex.normSq z + 8 / Complex.normSq (1 + 4 * z) +
          (f.roots.map (fun (a : ℝ) => 1 / Complex.normSq (z - a))).sum) =
          -z.im / Complex.normSq z + -8 * z.im / Complex.normSq (1 + 4 * z) +
            -z.im * (f.roots.map (fun (a : ℝ) => 1 / Complex.normSq (z - a))).sum := by ring
      _ = 0 := hi

end ResearchMain.EulerianPencil
