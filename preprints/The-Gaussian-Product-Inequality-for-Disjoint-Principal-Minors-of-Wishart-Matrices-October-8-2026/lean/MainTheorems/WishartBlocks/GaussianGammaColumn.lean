import MainTheorems.WishartBlocks.GaussianLinearLaplace
import MainTheorems.WishartBlocks.GammaLaplace
import Mathlib.MeasureTheory.Integral.Prod

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

noncomputable def columnQuadratic {n : ℕ} (a : ℝ)
    (b : EuclideanSpace ℝ (Fin n)) (T : Matrix (Fin n) (Fin n) ℝ)
    (d : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  a * d ^ 2 + 2 * d * ⟪b, z⟫_ℝ + ⟪z, T.toEuclideanLin z⟫_ℝ

noncomputable def columnSchur {n : ℕ} (a : ℝ)
    (b : EuclideanSpace ℝ (Fin n)) (T : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  a - 2 * ⟪b, ((1 + (2 : ℝ) • T)⁻¹).toEuclideanLin b⟫_ℝ

theorem columnSchur_nonneg {n : ℕ} {a : ℝ}
    {b : EuclideanSpace ℝ (Fin n)} {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.PosSemidef) (hQ : ∀ d z, 0 ≤ columnQuadratic a b T d z) :
    0 ≤ columnSchur a b T := by
  let y := ((1 + (2 : ℝ) • T)⁻¹).toEuclideanLin b
  have hdet : IsUnit (1 + (2 : ℝ) • T).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [matrix_one_add_smul_det hT.1]
    apply (Finset.prod_pos _).ne'
    intro i _
    have hEig := hT.eigenvalues_nonneg i
    positivity
  have hy : (1 + (2 : ℝ) • T).toEuclideanLin y = b := by
    dsimp [y]
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      Matrix.mul_nonsing_inv _ hdet, Matrix.toLpLin_one]
    rfl
  have hb : b = y + (2 : ℝ) • T.toEuclideanLin y := by
    rw [← hy, map_add, map_smul, Matrix.toLpLin_one]
    rfl
  have hI : ⟪b, y⟫_ℝ = ⟪y, y⟫_ℝ + 2 * ⟪y, T.toEuclideanLin y⟫_ℝ := by
    nth_rw 1 [hb]
    rw [inner_add_left, real_inner_smul_left, real_inner_comm (T.toEuclideanLin y) y]
  have hq := hQ 1 ((-2 : ℝ) • y)
  have he : columnQuadratic a b T 1 ((-2 : ℝ) • y) =
      a - 4 * ⟪b, y⟫_ℝ + 4 * ⟪y, T.toEuclideanLin y⟫_ℝ := by
    unfold columnQuadratic
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right]
    ring
  rw [he] at hq
  change 0 ≤ a - 2 * ⟪b, y⟫_ℝ
  nlinarith [real_inner_self_nonneg (x := y)]

theorem gaussian_column_laplace {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.PosSemidef) (a d : ℝ) (b : EuclideanSpace ℝ (Fin n)) :
    ∫ z : EuclideanSpace ℝ (Fin n), Real.exp (-columnQuadratic a b T d z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (Real.sqrt ((1 + (2 : ℝ) • T).det))⁻¹ *
        Real.exp (-(columnSchur a b T * d ^ 2)) := by
  let u := (-2 * d) • b
  have he : ∀ z, Real.exp (-columnQuadratic a b T d z) =
      Real.exp (-(a * d ^ 2)) *
        Real.exp (-⟪z, T.toEuclideanLin z⟫_ℝ + ⟪u, z⟫_ℝ) := by
    intro z
    rw [← Real.exp_add]
    congr 1
    dsimp [columnQuadratic, u]
    rw [real_inner_smul_left]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul,
    matrix_gaussian_linear_laplace hT u]
  have hu : ⟪u, ((1 + (2 : ℝ) • T)⁻¹).toEuclideanLin u⟫_ℝ =
      4 * d ^ 2 * ⟪b, ((1 + (2 : ℝ) • T)⁻¹).toEuclideanLin b⟫_ℝ := by
    dsimp [u]
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hu]
  calc
    _ = (Real.sqrt ((1 + (2 : ℝ) • T).det))⁻¹ *
        Real.exp (-(a * d ^ 2) +
          (4 * d ^ 2 * ⟪b, ((1 + (2 : ℝ) • T)⁻¹).toEuclideanLin b⟫_ℝ) / 2) := by
            rw [Real.exp_add]
            ring
    _ = _ := by unfold columnSchur; congr 2; ring

theorem gamma_half_rate_laplace {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    ∫ x : ℝ, Real.exp (-(t * x)) ∂(gammaMeasure s (1 / 2)) =
      (1 + 2 * t) ^ (-s) := by
  have hD : 0 < 1 + 2 * t := by positivity
  rw [gamma_laplace hs (by norm_num) (by positivity)]
  have he : ((1 / 2 : ℝ) / (1 / 2 + t)) = (1 + 2 * t)⁻¹ := by
    field_simp
  rw [he, Real.inv_rpow hD.le, ← Real.rpow_neg hD.le]

noncomputable def gammaColumnKernel {n : ℕ} (a : ℝ)
    (b : EuclideanSpace ℝ (Fin n)) (T : Matrix (Fin n) (Fin n) ℝ)
    (xz : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-columnQuadratic a b T (Real.sqrt xz.1) xz.2)

theorem gammaColumnKernel_integrable {n : ℕ} {a s : ℝ}
    {b : EuclideanSpace ℝ (Fin n)} {T : Matrix (Fin n) (Fin n) ℝ}
    (hs : 0 < s) (hQ : ∀ d z, 0 ≤ columnQuadratic a b T d z) :
    Integrable (gammaColumnKernel a b T)
      ((gammaMeasure s (1 / 2)).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let : IsProbabilityMeasure (gammaMeasure s (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure hs (by norm_num)
  apply (integrable_const (1 : ℝ)).mono' (by
    unfold gammaColumnKernel columnQuadratic
    fun_prop)
  exact ae_of_all _ fun xz => by
    unfold gammaColumnKernel
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hQ _ _))

theorem gamma_column_laplace {n : ℕ} {a s : ℝ}
    {b : EuclideanSpace ℝ (Fin n)} {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.PosSemidef) (hs : 0 < s)
    (hQ : ∀ d z, 0 ≤ columnQuadratic a b T d z) :
    ∫ xz, gammaColumnKernel a b T xz
        ∂((gammaMeasure s (1 / 2)).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      (Real.sqrt ((1 + (2 : ℝ) • T).det))⁻¹ *
        (1 + 2 * columnSchur a b T) ^ (-s) := by
  let : IsProbabilityMeasure (gammaMeasure s (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure hs (by norm_num)
  rw [integral_prod _ (gammaColumnKernel_integrable hs hQ)]
  unfold gammaColumnKernel
  simp_rw [gaussian_column_laplace hT]
  rw [integral_const_mul]
  have he : (fun x : ℝ => Real.exp (-(columnSchur a b T * (Real.sqrt x) ^ 2))) =ᵐ[
      gammaMeasure s (1 / 2)] fun x => Real.exp (-(columnSchur a b T * x)) := by
    filter_upwards [gammaMeasure_ae_positive s (1 / 2)] with x hx
    rw [Real.sq_sqrt hx.le]
  rw [integral_congr_ae he, gamma_half_rate_laplace hs (columnSchur_nonneg hT hQ)]

end ResearchMain.WishartBlocks
