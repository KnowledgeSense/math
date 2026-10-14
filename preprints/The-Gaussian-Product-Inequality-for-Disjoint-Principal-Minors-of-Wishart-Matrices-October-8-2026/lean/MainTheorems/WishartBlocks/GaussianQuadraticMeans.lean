import MainTheorems.WishartBlocks.GaussianFiniteQuadratic
import MainTheorems.WishartBlocks.MatrixGaussianLaplace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal InnerProductSpace

noncomputable def coordinateReflection {n : ℕ} (s : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if 0 ≤ s i then x i else -x i

theorem coordinateReflection_measurable {n : ℕ} (s : Fin n → ℝ) :
    Measurable (coordinateReflection s) := by
  apply Measurable.of_eval
  intro i
  by_cases hs : 0 ≤ s i
  · simpa only [coordinateReflection, hs, ite_true] using measurable_pi_apply i
  · simp only [coordinateReflection, hs, ite_false]
    fun_prop

theorem coordinateReflection_gaussian_pi {n : ℕ} (s : Fin n → ℝ) (v : Fin n → ℝ≥0) :
    (Measure.pi fun i => gaussianReal 0 (v i)).map (coordinateReflection s) =
      Measure.pi fun i => gaussianReal 0 (v i) := by
  classical
  let f : Fin n → ℝ → ℝ := fun i => if 0 ≤ s i then id else fun x => -x
  have hf : ∀ i, Measurable (f i) := by
    intro i
    by_cases hs : 0 ≤ s i <;> simp only [f, hs, ite_true, ite_false] <;> fun_prop
  have he : coordinateReflection s = fun x i => f i (x i) := by
    funext x i
    dsimp [coordinateReflection, f]
    split_ifs <;> rfl
  rw [he, Measure.pi_map_pi (fun i => (hf i).aemeasurable)]
  apply congrArg Measure.pi
  funext i
  by_cases hs : 0 ≤ s i
  · simp only [f, hs, ite_true, Measure.map_id]
  · simpa only [f, hs, ite_false, neg_zero] using
      (gaussianReal_map_neg (μ := (0 : ℝ)) (v := v i))

theorem gaussianPiQuadraticPower_abs_mean {n : ℕ} (c : ℝ) (d : Fin n → ℝ) (b : ℝ)
    (v : Fin n → ℝ≥0) (s : Fin n → ℝ) :
    gaussianPiQuadraticPower c d b v (fun i => |s i|) =
      gaussianPiQuadraticPower c d b v s := by
  unfold gaussianPiQuadraticPower
  nth_rw 1 [← coordinateReflection_gaussian_pi s v]
  rw [integral_map (coordinateReflection_measurable s).aemeasurable
    ((by fun_prop : Measurable (fun x : Fin n → ℝ =>
      (c + ∑ i, d i * (x i + |s i|) ^ 2) ^ b)).aestronglyMeasurable)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    apply congrArg (fun y : ℝ => (c + y) ^ b)
    apply Finset.sum_congr rfl
    intro i _
    by_cases hs : 0 ≤ s i
    · simp only [coordinateReflection, hs, ite_true, abs_of_nonneg hs]
    · have hs' : s i ≤ 0 := (lt_of_not_ge hs).le
      simp only [coordinateReflection, hs, ite_false, abs_of_nonpos hs']
      ring

theorem gaussianPiQuadraticPower_ray_monotone {n : ℕ} {c b : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≠ 0) (m : Fin n → ℝ) :
    MonotoneOn (fun θ => gaussianPiQuadraticPower c d b v
      (fun i => Real.sqrt θ * m i)) (Set.Ici 0) := by
  intro θ hθ η hη hθη
  change gaussianPiQuadraticPower c d b v (fun i => Real.sqrt θ * m i) ≤
    gaussianPiQuadraticPower c d b v (fun i => Real.sqrt η * m i)
  rw [← gaussianPiQuadraticPower_abs_mean c d b v (fun i => Real.sqrt θ * m i),
    ← gaussianPiQuadraticPower_abs_mean c d b v (fun i => Real.sqrt η * m i)]
  apply gaussianPiQuadraticPower_monotone hc hb d hd v hv
  · exact fun i => abs_nonneg _
  · exact fun i => abs_nonneg _
  · intro i
    change |Real.sqrt θ * m i| ≤ |Real.sqrt η * m i|
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg θ),
      abs_of_nonneg (Real.sqrt_nonneg η)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hθη) (abs_nonneg _)

theorem basisSynthesis_measurable {n : ℕ} (B : OrthonormalBasis (Fin n) ℝ
    (EuclideanSpace ℝ (Fin n))) :
    Measurable (fun x : Fin n → ℝ => ∑ i, x i • B i) :=
  (by fun_prop : Continuous (fun x : Fin n → ℝ => ∑ i, x i • B i)).measurable

theorem gaussian_matrix_quadratic_integrand_diagonal {n : ℕ} (c b : ℝ)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (m : EuclideanSpace ℝ (Fin n)) (x : Fin n → ℝ) :
    (c + ⟪(∑ i, x i • hA.1.eigenvectorBasis i) + m,
      A.toEuclideanLin ((∑ i, x i • hA.1.eigenvectorBasis i) + m)⟫_ℝ) ^ b =
    (c + ∑ i, hA.1.eigenvalues i * (x i + hA.1.eigenvectorBasis.repr m i) ^ 2) ^ b := by
  rw [matrix_quadratic_eigenbasis hA.1]
  apply congrArg (fun y : ℝ => (c + y) ^ b)
  have hr : hA.1.eigenvectorBasis.repr ((∑ i, x i • hA.1.eigenvectorBasis i) + m) =
      WithLp.toLp 2 x + hA.1.eigenvectorBasis.repr m := by
    rw [map_add, orthonormalBasis_repr_sum]
  rw [hr]
  rfl

theorem gaussian_matrix_quadratic_integrable {n : ℕ} {c b : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (m : EuclideanSpace ℝ (Fin n)) :
    Integrable
      (fun z : EuclideanSpace ℝ (Fin n) =>
        (c + ⟪z + m, A.toEuclideanLin (z + m)⟫_ℝ) ^ b)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis hA.1.eigenvectorBasis]
  apply (integrable_map_measure
    ((by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
      (c + ⟪z + m, A.toEuclideanLin (z + m)⟫_ℝ) ^ b)).aestronglyMeasurable)
    (basisSynthesis_measurable hA.1.eigenvectorBasis).aemeasurable).mpr
  have hi := gaussian_pi_quadratic_integrable hc hb hA.1.eigenvalues
    (fun i => hA.1.eigenvectorBasis.repr m i) hA.eigenvalues_nonneg (fun _ => 1)
  exact hi.congr (ae_of_all _ fun x =>
    (gaussian_matrix_quadratic_integrand_diagonal c b hA m x).symm)

theorem gaussian_matrix_quadratic_diagonal {n : ℕ} (c b : ℝ)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (m : EuclideanSpace ℝ (Fin n)) :
    (∫ z : EuclideanSpace ℝ (Fin n),
        (c + ⟪z + m, A.toEuclideanLin (z + m)⟫_ℝ) ^ b
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      gaussianPiQuadraticPower c hA.1.eigenvalues b (fun _ => 1)
        (fun i => hA.1.eigenvectorBasis.repr m i) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis hA.1.eigenvectorBasis,
    integral_map (basisSynthesis_measurable hA.1.eigenvectorBasis).aemeasurable
      ((by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
        (c + ⟪z + m, A.toEuclideanLin (z + m)⟫_ℝ) ^ b)).aestronglyMeasurable)]
  exact integral_congr_ae (ae_of_all _ fun x =>
    gaussian_matrix_quadratic_integrand_diagonal c b hA m x)

theorem gaussian_matrix_quadratic_ray_monotone {n : ℕ} {c b : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (v : EuclideanSpace ℝ (Fin n)) :
    MonotoneOn
      (fun θ => ∫ z : EuclideanSpace ℝ (Fin n),
        (c + ⟪z + Real.sqrt θ • v,
          A.toEuclideanLin (z + Real.sqrt θ • v)⟫_ℝ) ^ b
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) (Set.Ici 0) := by
  simp_rw [gaussian_matrix_quadratic_diagonal c b hA,
    map_smul, PiLp.smul_apply, smul_eq_mul]
  exact gaussianPiQuadraticPower_ray_monotone hc hb hA.1.eigenvalues
    hA.eigenvalues_nonneg (fun _ => 1) (by simp)
      (fun i => hA.1.eigenvectorBasis.repr v i)

end ResearchMain.WishartBlocks
