import MainTheorems.WishartBlocks.NoncentralPolynomialMoments

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators InnerProductSpace MatrixOrder Matrix.Norms.Elementwise NNReal ENNReal

abbrev OneRowInput (p : ℕ) := Matrix (Fin p) (Fin p) ℝ × EuclideanSpace ℝ (Fin p)

noncomputable def oneRowInputLaw {p : ℕ} (q : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (OneRowInput p) :=
  (bartlettLaw (q - 1) S).prod (stdGaussian (EuclideanSpace ℝ (Fin p)))

theorem oneRowInput_probability {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) : IsProbabilityMeasure (oneRowInputLaw q S) := by
  let : IsProbabilityMeasure (bartlettLaw (q - 1) S) :=
    bartlett_law_probability (by linarith) S
  unfold oneRowInputLaw
  infer_instance

theorem oneRowInput_positiveSemidefinite {p : ℕ} (q : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) :
    ∀ᵐ x ∂(oneRowInputLaw q S), x.1.PosSemidef :=
  Measure.quasiMeasurePreserving_fst.ae (bartlettLaw_positiveSemidefinite (q - 1) S)

theorem oneRowInput_polynomial_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    Integrable (fun x : OneRowInput p => (1 + ‖x‖) ^ k) (oneRowInputLaw q S) := by
  have hg : Integrable (fun z : EuclideanSpace ℝ (Fin p) => (1 + ‖z‖) ^ k)
      (stdGaussian (EuclideanSpace ℝ (Fin p))) :=
    polynomial_integrable_of_memLp k
      (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin p)))
        (k : ℝ≥0∞) (by simp))
  apply ((bartlett_polynomial_integrable (by linarith) S k).mul_prod hg).mono' (by fun_prop)
  exact ae_of_all _ fun x => by
    have hx : 1 + ‖x‖ ≤ (1 + ‖x.1‖) * (1 + ‖x.2‖) := by
      have hn : ‖x‖ ≤ ‖x.1‖ + ‖x.2‖ := by
        rw [Prod.norm_def]
        exact max_le (le_add_of_nonneg_right (norm_nonneg _))
          (le_add_of_nonneg_left (norm_nonneg _))
      nlinarith [norm_nonneg x.1, norm_nonneg x.2]
    rw [Real.norm_of_nonneg (by positivity)]
    exact (pow_le_pow_left₀ (by positivity) hx k).trans_eq (mul_pow _ _ _)

theorem oneRowInput_real_growth_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    (S : Matrix (Fin p) (Fin p) ℝ) {f : OneRowInput p → ℝ} (hf : Measurable f)
    {C β : ℝ} (hC : 0 ≤ C) (hB : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ β) :
    Integrable f (oneRowInputLaw q S) := by
  let k := ⌈β⌉₊
  apply ((oneRowInput_polynomial_integrable hq S k).const_mul C).mono' hf.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    calc
      ‖f x‖ ≤ C * (1 + ‖x‖) ^ β := hB x
      _ ≤ C * (1 + ‖x‖) ^ k := by
        rw [← Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) (Nat.le_ceil β)) hC

noncomputable def oneRowGaussianVector {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : OneRowInput p) : EuclideanSpace ℝ (Fin p) :=
  (CFC.sqrt S).toEuclideanLin x.2 + s • v

noncomputable def oneRowGaussianBound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : ℝ :=
  ‖(CFC.sqrt S).toEuclideanLin.toContinuousLinearMap‖ + (|s| + 1) * ‖v‖

theorem oneRowGaussianBound_nonneg {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) : 0 ≤ oneRowGaussianBound S v s := by
  unfold oneRowGaussianBound
  positivity

theorem oneRowGaussianVector_local_bound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) {t : ℝ} (ht : |t - s| < 1)
    (x : OneRowInput p) :
    ‖oneRowGaussianVector S v t x‖ ≤ oneRowGaussianBound S v s * (1 + ‖x‖) := by
  have ht' : |t| ≤ |s| + 1 := by
    have h := abs_add_le (t - s) s
    have he : t - s + s = t := by ring
    rw [he] at h
    linarith
  have hR := (CFC.sqrt S).toEuclideanLin.toContinuousLinearMap.le_opNorm x.2
  calc
    _ ≤ ‖(CFC.sqrt S).toEuclideanLin x.2‖ + ‖t • v‖ := norm_add_le _ _
    _ ≤ ‖(CFC.sqrt S).toEuclideanLin.toContinuousLinearMap‖ * ‖x.2‖ + (|s| + 1) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hR (mul_le_mul_of_nonneg_right ht' (norm_nonneg v))
    _ ≤ oneRowGaussianBound S v s * (1 + ‖x‖) := by
      have hx : ‖x.2‖ ≤ 1 + ‖x‖ := (norm_snd_le x).trans (by linarith)
      have hb : 0 ≤ (|s| + 1) * ‖v‖ := by positivity
      dsimp [oneRowGaussianBound]
      calc
        _ ≤ ‖(CFC.sqrt S).toEuclideanLin.toContinuousLinearMap‖ * (1 + ‖x‖) +
            ((|s| + 1) * ‖v‖) * (1 + ‖x‖) :=
          add_le_add (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
            (le_mul_of_one_le_right hb (by linarith [norm_nonneg x]))
        _ = _ := by ring

theorem oneRowWishartValue_positive {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) {x : OneRowInput p} (hx : x.1.PosSemidef) :
    (oneRowWishartValue S (s • v) x).PosSemidef := by
  apply hx.add
  simpa only [gaussianMeanGram, oneRowGaussianVector, star_trivial] using
    Matrix.posSemidef_vecMulVec_self_star (fun i => oneRowGaussianVector S v s x i)

end ResearchMain.WishartBlocks
