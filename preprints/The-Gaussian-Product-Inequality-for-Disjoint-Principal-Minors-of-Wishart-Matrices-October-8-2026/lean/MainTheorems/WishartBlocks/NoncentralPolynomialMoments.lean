import MainTheorems.WishartBlocks.NoncentralWishartLaw
import MainTheorems.WishartBlocks.WishartIntegrability
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.Pi

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise NNReal ENNReal

theorem polynomial_integrable_of_memLp {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    (k : ℕ) (hX : MemLp (id : E → E) (k : ℝ≥0∞) μ) :
    Integrable (fun x : E => (1 + ‖x‖) ^ k) μ := by
  have hI := hX.integrable_norm_pow' (p := k)
  apply (((integrable_const 1).add hI).const_mul ((2 : ℝ) ^ (k - 1))).mono'
    (by fun_prop)
  exact ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (by positivity)]
    change (1 + ‖x‖) ^ k ≤ (2 : ℝ) ^ (k - 1) * (1 + ‖x‖ ^ k)
    simpa only [one_pow] using add_pow_le (zero_le_one (α := ℝ)) (norm_nonneg x) k

theorem bartlett_polynomial_integrable {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (S : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    Integrable (fun W : Matrix (Fin p) (Fin p) ℝ => (1 + ‖W‖) ^ k) (bartlettLaw α S) := by
  have hg : Measurable (fun W : Matrix (Fin p) (Fin p) ℝ => (1 + ‖W‖) ^ k) := by fun_prop
  unfold bartlettLaw
  apply (integrable_map_measure hg.aestronglyMeasurable (measurable_bartlettValue S).aemeasurable).mpr
  let C := bartlettEntryConstant S
  have hC : 0 ≤ C := bartlettEntryConstant_nonneg S
  apply bartlett_real_growth_integrable hα (hg.comp (measurable_bartlettValue S))
    (pow_nonneg (by positivity : 0 ≤ 1 + C) k)
  intro x
  have hV : ‖bartlettValue S x‖ ≤ C * (1 + ‖x‖) ^ 2 :=
    (Matrix.norm_le_iff (by positivity)).mpr (bartlettValue_entry_bound S x)
  have hB : 1 + ‖bartlettValue S x‖ ≤ (1 + C) * (1 + ‖x‖) ^ 2 := by
    nlinarith [norm_nonneg x]
  calc
    ‖(1 + ‖bartlettValue S x‖) ^ k‖ = (1 + ‖bartlettValue S x‖) ^ k :=
      Real.norm_of_nonneg (by positivity)
    _ ≤ ((1 + C) * (1 + ‖x‖) ^ 2) ^ k := pow_le_pow_left₀ (by positivity) hB k
    _ = (1 + C) ^ k * (1 + ‖x‖) ^ ((2 * k : ℕ) : ℝ) := by
      rw [mul_pow, ← pow_mul, Real.rpow_natCast]

theorem gaussian_rows_polynomial_integrable (p r k : ℕ) :
    Integrable (fun z : Fin r → EuclideanSpace ℝ (Fin p) => (1 + ‖z‖) ^ k)
      (Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin p))) := by
  apply polynomial_integrable_of_memLp k
  apply MemLp.of_eval
  intro i
  simpa only [Function.comp_def, id_eq, Function.eval] using
    (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin p)))
      (k : ℝ≥0∞) (by simp)).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin p))) i)

theorem euclidean_matrix_entry_norm_bound {p : ℕ}
    (R : Matrix (Fin p) (Fin p) ℝ) (z : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    ‖R.toEuclideanLin z i‖ ≤ (p : ℝ) * ‖R‖ * ‖z‖ := by
  change ‖∑ j, R i j * z j‖ ≤ _
  calc
    ‖∑ j, R i j * z j‖ ≤ ∑ j, ‖R i j * z j‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin p, ‖R‖ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm R)
        (PiLp.norm_apply_le z j) (norm_nonneg _) (norm_nonneg R)
    _ = _ := by simp [mul_assoc]

theorem gaussianMeanGram_norm_bound {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (m z : EuclideanSpace ℝ (Fin p)) :
    ‖gaussianMeanGram S m z‖ ≤
      ((p : ℝ) * ‖CFC.sqrt S‖ + ‖m‖) ^ 2 * (1 + ‖z‖) ^ 2 := by
  have hy : ∀ i, ‖((CFC.sqrt S).toEuclideanLin z + m) i‖ ≤
      ((p : ℝ) * ‖CFC.sqrt S‖ + ‖m‖) * (1 + ‖z‖) := by
    intro i
    calc
      ‖((CFC.sqrt S).toEuclideanLin z + m) i‖ ≤
          ‖(CFC.sqrt S).toEuclideanLin z i‖ + ‖m i‖ := norm_add_le _ _
      _ ≤ (p : ℝ) * ‖CFC.sqrt S‖ * ‖z‖ + ‖m‖ :=
        add_le_add (euclidean_matrix_entry_norm_bound _ z i) (PiLp.norm_apply_le m i)
      _ ≤ _ := by nlinarith [norm_nonneg z, norm_nonneg m, norm_nonneg (CFC.sqrt S)]
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  simp only [gaussianMeanGram, Matrix.vecMulVec_apply, norm_mul]
  calc
    _ ≤ (((p : ℝ) * ‖CFC.sqrt S‖ + ‖m‖) * (1 + ‖z‖)) *
        (((p : ℝ) * ‖CFC.sqrt S‖ + ‖m‖) * (1 + ‖z‖)) :=
      mul_le_mul (hy i) (hy j) (norm_nonneg _) (by positivity)
    _ = _ := by ring

noncomputable def noncentralGrowthConstant {p r : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (M : Fin r → EuclideanSpace ℝ (Fin p)) : ℝ :=
  (r : ℝ) * ((p : ℝ) * ‖CFC.sqrt S‖ + ‖M‖) ^ 2

theorem noncentralWishartValue_norm_bound {p r : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (M : Fin r → EuclideanSpace ℝ (Fin p))
    (wz : Matrix (Fin p) (Fin p) ℝ × (Fin r → EuclideanSpace ℝ (Fin p))) :
    ‖noncentralWishartValue S M wz‖ ≤
      ‖wz.1‖ + noncentralGrowthConstant S M * (1 + ‖wz.2‖) ^ 2 := by
  unfold noncentralWishartValue
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  calc
    ‖∑ i, gaussianMeanGram S (M i) (wz.2 i)‖ ≤
        ∑ i, ‖gaussianMeanGram S (M i) (wz.2 i)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin r,
        ((p : ℝ) * ‖CFC.sqrt S‖ + ‖M‖) ^ 2 * (1 + ‖wz.2‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply (gaussianMeanGram_norm_bound S (M i) (wz.2 i)).trans
      gcongr
      · exact norm_le_pi_norm M i
      · exact norm_le_pi_norm wz.2 i
    _ = _ := by simp [noncentralGrowthConstant, mul_assoc]

theorem noncentralWishart_polynomial_integrable {p r : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ))
    (S : Matrix (Fin p) (Fin p) ℝ) (M : Fin r → EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    Integrable (fun W : Matrix (Fin p) (Fin p) ℝ => (1 + ‖W‖) ^ k)
      (noncentralWishartLaw α S M) := by
  let : IsProbabilityMeasure (bartlettLaw (α - (r : ℝ)) S) := bartlett_law_probability hα S
  let C := noncentralGrowthConstant S M
  have hC : 0 ≤ C := by dsimp [C, noncentralGrowthConstant]; positivity
  have hg : Measurable (fun W : Matrix (Fin p) (Fin p) ℝ => (1 + ‖W‖) ^ k) := by fun_prop
  unfold noncentralWishartLaw
  apply (integrable_map_measure hg.aestronglyMeasurable
    (measurable_noncentralWishartValue S M).aemeasurable).mpr
  have hi := (bartlett_polynomial_integrable hα S k).mul_prod
    (gaussian_rows_polynomial_integrable p r (2 * k))
  apply (hi.const_mul ((1 + C) ^ k)).mono'
    (hg.comp (measurable_noncentralWishartValue S M)).aestronglyMeasurable
  exact ae_of_all _ fun wz => by
    dsimp only [Function.comp_def]
    have hV : ‖noncentralWishartValue S M wz‖ ≤ ‖wz.1‖ + C * (1 + ‖wz.2‖) ^ 2 :=
      noncentralWishartValue_norm_bound S M wz
    have hn : 0 ≤ ‖wz.1‖ := norm_nonneg _
    have hz : 0 ≤ ‖wz.2‖ := norm_nonneg _
    have hB : 1 + ‖noncentralWishartValue S M wz‖ ≤
        (1 + C) * (1 + ‖wz.1‖) * (1 + ‖wz.2‖) ^ 2 := by
      have hp : 1 ≤ (1 + ‖wz.2‖) ^ 2 := by nlinarith
      have hp' : 1 + ‖wz.1‖ ≤ (1 + ‖wz.1‖) * (1 + ‖wz.2‖) ^ 2 := by nlinarith
      have hCp : C * (1 + ‖wz.2‖) ^ 2 ≤
          C * (1 + ‖wz.1‖) * (1 + ‖wz.2‖) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hC hn]) (sq_nonneg _)
      calc
        1 + ‖noncentralWishartValue S M wz‖ ≤
            (1 + ‖wz.1‖) + C * (1 + ‖wz.2‖) ^ 2 := by linarith
        _ ≤ (1 + ‖wz.1‖) * (1 + ‖wz.2‖) ^ 2 +
            C * (1 + ‖wz.1‖) * (1 + ‖wz.2‖) ^ 2 := add_le_add hp' hCp
        _ = _ := by ring
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ ((1 + C) * (1 + ‖wz.1‖) * (1 + ‖wz.2‖) ^ 2) ^ k :=
        pow_le_pow_left₀ (by positivity) hB k
      _ = _ := by rw [mul_pow, mul_pow, ← pow_mul]; ring

theorem noncentralWishart_real_growth_integrable {p r : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α - (r : ℝ))
    (S : Matrix (Fin p) (Fin p) ℝ) (M : Fin r → EuclideanSpace ℝ (Fin p))
    {f : Matrix (Fin p) (Fin p) ℝ → ℝ} (hf : Measurable f)
    {C β : ℝ} (hC : 0 ≤ C) (hb : ∀ W, ‖f W‖ ≤ C * (1 + ‖W‖) ^ β) :
    Integrable f (noncentralWishartLaw α S M) := by
  let k := ⌈β⌉₊
  apply ((noncentralWishart_polynomial_integrable hα S M k).const_mul C).mono'
    hf.aestronglyMeasurable
  exact ae_of_all _ fun W => by
    calc
      ‖f W‖ ≤ C * (1 + ‖W‖) ^ β := hb W
      _ ≤ C * (1 + ‖W‖) ^ k := by
        rw [← Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg W]) (Nat.le_ceil β)) hC

end ResearchMain.WishartBlocks
