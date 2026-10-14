import MainTheorems.WishartBlocks.OneRowMoments
import MainTheorems.WishartBlocks.LaplaceTestDerivatives
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped BigOperators InnerProductSpace Topology Matrix.Norms.Elementwise MatrixOrder

noncomputable def gaussianMeanLaplace {p : ℕ} (S T : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) : ℝ :=
  laplaceMatrixTest T (oneRowWishartValue S (s • v) x)

noncomputable def gaussianMeanLaplaceFirst {p : ℕ} (S T : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) : ℝ :=
  -2 * ⟪oneRowGaussianVector S v s x, T.toEuclideanLin v⟫_ℝ * gaussianMeanLaplace S T v s x

noncomputable def gaussianMeanLaplaceSecond {p : ℕ} (S T : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) : ℝ :=
  (4 * ⟪oneRowGaussianVector S v s x, T.toEuclideanLin v⟫_ℝ ^ 2 -
    2 * ⟪v, T.toEuclideanLin v⟫_ℝ) * gaussianMeanLaplace S T v s x

@[fun_prop] theorem gaussianMeanLaplace_measurable {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Measurable (gaussianMeanLaplace S T v s) :=
  (continuous_exp_trace_mul T).measurable.comp (measurable_oneRowWishartValue S (s • v))

@[fun_prop] theorem oneRowGaussianVector_measurable {p : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Measurable (oneRowGaussianVector S v s) :=
  ((CFC.sqrt S).toEuclideanLin.toContinuousLinearMap.continuous.measurable.comp
    measurable_snd).add_const (s • v)

@[fun_prop] theorem gaussianMeanLaplaceFirst_measurable {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Measurable (gaussianMeanLaplaceFirst S T v s) :=
  (((oneRowGaussianVector_measurable S v s).inner measurable_const).const_mul (-2)).fun_mul
    (gaussianMeanLaplace_measurable S T v s)

@[fun_prop] theorem gaussianMeanLaplaceSecond_measurable {p : ℕ}
    (S T : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Measurable (gaussianMeanLaplaceSecond S T v s) := by
  unfold gaussianMeanLaplaceSecond
  fun_prop

theorem euclidean_symmetric_inner {p : ℕ} {T : Matrix (Fin p) (Fin p) ℝ}
    (hT : T.IsHermitian) (u v : EuclideanSpace ℝ (Fin p)) :
    ⟪v, T.toEuclideanLin u⟫_ℝ = ⟪u, T.toEuclideanLin v⟫_ℝ := by
  rw [← euclidean_dotProduct_matrix, ← euclidean_dotProduct_matrix]
  exact symmetric_matrix_quadratic_comm T hT.isSymm _ _

theorem gaussianMeanLaplace_quadratic {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.IsHermitian)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    gaussianMeanLaplace S T v s x = Real.exp (-((T * x.1).trace +
      ⟪(CFC.sqrt S).toEuclideanLin x.2, T.toEuclideanLin ((CFC.sqrt S).toEuclideanLin x.2)⟫_ℝ +
      2 * s * ⟪(CFC.sqrt S).toEuclideanLin x.2, T.toEuclideanLin v⟫_ℝ +
      s ^ 2 * ⟪v, T.toEuclideanLin v⟫_ℝ)) := by
  simp only [gaussianMeanLaplace, laplaceMatrixTest, oneRowWishartValue,
    Matrix.mul_add, Matrix.trace_add, trace_gaussianMeanGram, map_add, map_smul,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [euclidean_symmetric_inner hT v ((CFC.sqrt S).toEuclideanLin x.2)]
  congr 1
  ring_nf

theorem gaussianMeanLaplace_hasDerivAt {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.IsHermitian)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    HasDerivAt (fun t => gaussianMeanLaplace S T v t x)
      (gaussianMeanLaplaceFirst S T v s x) s := by
  let a := ⟪(CFC.sqrt S).toEuclideanLin x.2, T.toEuclideanLin v⟫_ℝ
  let b := ⟪v, T.toEuclideanLin v⟫_ℝ
  let c := (T * x.1).trace +
    ⟪(CFC.sqrt S).toEuclideanLin x.2, T.toEuclideanLin ((CFC.sqrt S).toEuclideanLin x.2)⟫_ℝ
  have h := ((hasDerivAt_const s c).add
    (((hasDerivAt_id' s).const_mul (2 * a)).add ((hasDerivAt_id' s).pow 2 |>.mul_const b))).neg.exp
  convert h using 1
  · funext t
    rw [gaussianMeanLaplace_quadratic S hT]
    dsimp [a, b, c]
    congr 1
    ring_nf
  · rw [gaussianMeanLaplaceFirst, gaussianMeanLaplace_quadratic S hT]
    simp only [oneRowGaussianVector, inner_add_left, real_inner_smul_left]
    dsimp [a, b, c]
    ring_nf

theorem gaussianMeanLaplaceFirst_hasDerivAt {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.IsHermitian)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) :
    HasDerivAt (fun t => gaussianMeanLaplaceFirst S T v t x)
      (gaussianMeanLaplaceSecond S T v s x) s := by
  let a := ⟪(CFC.sqrt S).toEuclideanLin x.2, T.toEuclideanLin v⟫_ℝ
  let b := ⟪v, T.toEuclideanLin v⟫_ℝ
  have h := (((hasDerivAt_const s a).add ((hasDerivAt_id' s).mul_const b)).const_mul (-2)).mul
    (gaussianMeanLaplace_hasDerivAt S hT v s x)
  convert h using 1
  · funext t
    simp only [gaussianMeanLaplaceFirst, oneRowGaussianVector, inner_add_left,
      real_inner_smul_left]
    rfl
  · dsimp [gaussianMeanLaplaceSecond, gaussianMeanLaplaceFirst,
      oneRowGaussianVector, a, b]
    simp only [inner_add_left, real_inner_smul_left]
    ring_nf

theorem gaussianMeanLaplace_bound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) {x : OneRowInput p} (hx : x.1.PosSemidef) :
    0 ≤ gaussianMeanLaplace S T v s x ∧ gaussianMeanLaplace S T v s x ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (trace_positive_product hT (oneRowWishartValue_positive S v s hx))

theorem gaussianMeanLaplaceFirst_local_bound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) {t : ℝ} (ht : |t - s| < 1)
    {x : OneRowInput p} (hx : x.1.PosSemidef) :
    ‖gaussianMeanLaplaceFirst S T v t x‖ ≤
      (2 * ‖T.toEuclideanLin v‖ * oneRowGaussianBound S v s) * (1 + ‖x‖) := by
  have hg := gaussianMeanLaplace_bound S hT v t hx
  have hC := oneRowGaussianBound_nonneg S v s
  have hi : |⟪oneRowGaussianVector S v t x, T.toEuclideanLin v⟫_ℝ| ≤
      ‖T.toEuclideanLin v‖ * oneRowGaussianBound S v s * (1 + ‖x‖) := by
    calc
      _ ≤ ‖oneRowGaussianVector S v t x‖ * ‖T.toEuclideanLin v‖ := abs_real_inner_le_norm _ _
      _ ≤ (oneRowGaussianBound S v s * (1 + ‖x‖)) * ‖T.toEuclideanLin v‖ :=
        mul_le_mul_of_nonneg_right (oneRowGaussianVector_local_bound S v s ht x) (norm_nonneg _)
      _ = _ := by ring_nf
  simp only [gaussianMeanLaplaceFirst, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg hg.1, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * (‖T.toEuclideanLin v‖ * oneRowGaussianBound S v s * (1 + ‖x‖)) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hi (by positivity)) hg.2 hg.1 (by positivity)
    _ = _ := by ring_nf

theorem gaussianMeanLaplaceSecond_local_bound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) {t : ℝ} (ht : |t - s| < 1)
    {x : OneRowInput p} (hx : x.1.PosSemidef) :
    ‖gaussianMeanLaplaceSecond S T v t x‖ ≤
      (4 * (‖T.toEuclideanLin v‖ * oneRowGaussianBound S v s) ^ 2 +
        2 * |⟪v, T.toEuclideanLin v⟫_ℝ|) * (1 + ‖x‖) ^ 2 := by
  let A := ‖T.toEuclideanLin v‖ * oneRowGaussianBound S v s
  let B := ⟪v, T.toEuclideanLin v⟫_ℝ
  let Q := ⟪oneRowGaussianVector S v t x, T.toEuclideanLin v⟫_ℝ
  have hA : 0 ≤ A := mul_nonneg (norm_nonneg _) (oneRowGaussianBound_nonneg S v s)
  have hQ : |Q| ≤ A * (1 + ‖x‖) := by
    apply (abs_real_inner_le_norm _ _).trans
    have h := mul_le_mul_of_nonneg_right (oneRowGaussianVector_local_bound S v s ht x)
      (norm_nonneg (T.toEuclideanLin v))
    simpa only [A, mul_assoc, mul_left_comm, mul_comm] using h
  have hQ2 : Q ^ 2 ≤ A ^ 2 * (1 + ‖x‖) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg Q) hQ 2
    simpa only [sq_abs, mul_pow] using h
  have hg := gaussianMeanLaplace_bound S hT v t hx
  have hC : |4 * Q ^ 2 - 2 * B| ≤ (4 * A ^ 2 + 2 * |B|) * (1 + ‖x‖) ^ 2 := by
    calc
      _ ≤ |4 * Q ^ 2| + |2 * B| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (4 * Q ^ 2) (2 * B)
      _ = 4 * Q ^ 2 + 2 * |B| := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 4 * Q ^ 2), abs_mul]
        norm_num
      _ ≤ (4 * A ^ 2 + 2 * |B|) * (1 + ‖x‖) ^ 2 := by
        have hx' : 1 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
        nlinarith [abs_nonneg B]
  rw [gaussianMeanLaplaceSecond, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hg.1]
  exact (mul_le_mul hC hg.2 hg.1 (by positivity)).trans_eq (mul_one _)

theorem gaussianMeanLaplace_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Integrable (gaussianMeanLaplace S T v s) (oneRowInputLaw q S) := by
  let : IsProbabilityMeasure (oneRowInputLaw q S) := oneRowInput_probability hq S
  apply (integrable_const (1 : ℝ)).mono'
    (gaussianMeanLaplace_measurable S T v s).aestronglyMeasurable
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  have h := gaussianMeanLaplace_bound S hT v s hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem gaussianMeanLaplaceFirst_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Integrable (gaussianMeanLaplaceFirst S T v s) (oneRowInputLaw q S) := by
  have hC := oneRowGaussianBound_nonneg S v s
  apply ((oneRowInput_polynomial_integrable hq S 1).const_mul
    (2 * ‖T.toEuclideanLin v‖ * oneRowGaussianBound S v s)).mono'
      (gaussianMeanLaplaceFirst_measurable S T v s).aestronglyMeasurable
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  simpa only [sub_self, abs_zero, pow_one,
    Real.norm_of_nonneg (by positivity : 0 ≤
      (2 * ‖T.toEuclideanLin v‖ * oneRowGaussianBound S v s) * (1 + ‖x‖))] using
    gaussianMeanLaplaceFirst_local_bound S hT v s (by simp) hx

theorem gaussianMeanLaplaceSecond_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) {T : Matrix (Fin p) (Fin p) ℝ} (hT : T.PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Integrable (gaussianMeanLaplaceSecond S T v s) (oneRowInputLaw q S) := by
  apply ((oneRowInput_polynomial_integrable hq S 2).const_mul
    (4 * (‖T.toEuclideanLin v‖ * oneRowGaussianBound S v s) ^ 2 +
      2 * |⟪v, T.toEuclideanLin v⟫_ℝ|)).mono'
      (gaussianMeanLaplaceSecond_measurable S T v s).aestronglyMeasurable
  filter_upwards [oneRowInput_positiveSemidefinite q S] with x hx
  simpa only [Real.norm_of_nonneg (by positivity : 0 ≤
    (4 * (‖T.toEuclideanLin v‖ * oneRowGaussianBound S v s) ^ 2 +
      2 * |⟪v, T.toEuclideanLin v⟫_ℝ|) * (1 + ‖x‖) ^ 2)] using
    gaussianMeanLaplaceSecond_local_bound S hT v s (by simp) hx

end ResearchMain.WishartBlocks
