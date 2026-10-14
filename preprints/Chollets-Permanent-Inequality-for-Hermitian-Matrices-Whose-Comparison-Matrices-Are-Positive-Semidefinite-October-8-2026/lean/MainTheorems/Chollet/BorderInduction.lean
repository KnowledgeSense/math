import MainTheorems.Chollet.PositiveCoefficients
import MainTheorems.Chollet.SquaredBorder
import MainTheorems.Chollet.ScalarBounds

noncomputable section

namespace ResearchMain.Chollet

open scoped ComplexOrder

variable {I : Type*} [Fintype I] [LinearOrder I]

omit [Fintype I] [LinearOrder I] in
theorem pencil_shift (B : Matrix I I ℂ) (x : I → ℂ) (t : ℝ) :
    pencil (pencil B x (-1)) x t = pencil B x (t - 1) := by
  ext i j
  simp only [pencil, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  push_cast
  ring

theorem rankPolynomial_eval_real (B : Matrix I I ℂ) (x : I → ℂ) (s : ℝ) :
    (rankPolynomial B x).eval (s : ℂ) = (pencil B x s).permanent := by
  rw [rankPolynomial_eval]
  apply congrArg Matrix.permanent
  funext i j
  simp [pencil, rankOne, Matrix.vecMulVec, Complex.real_smul]

theorem positive_border_square_bound {a : ℝ} {z : I → ℂ} {B : Matrix I I ℂ}
    (hA : ComparisonPD (border a z B)) (ha : 0 < a)
    (hchild : ∀ C : Matrix I I ℂ, ComparisonPSD C →
      (squaredEntries C).permanent ≤ C.permanent.re ^ 2) :
    (squaredEntries (border a z B)).permanent ≤ (border a z B).permanent.re ^ 2 := by
  let x := normalizedBorder a z
  let H := pencil B x (-1)
  have hclosure : ∀ t : ℝ, 0 ≤ t → t ≤ 2 → ComparisonPSD (pencil H x t) := by
    intro t ht ht'
    rw [show pencil H x t = pencil B x (t - 1) from pencil_shift B x t]
    exact border_pencil_closure hA.toPSD ha t ht ht'
  have hH : ComparisonPSD H := by
    have h := hclosure 0 le_rfl (by norm_num)
    simpa [pencil] using h
  have hB : ComparisonPSD B := by
    have h := hclosure 1 (by norm_num) (by norm_num)
    rw [show pencil H x 1 = pencil B x (1 - 1) from pencil_shift B x 1] at h
    simpa [pencil] using h
  have hone : pencil H x 1 = B := by
    rw [show pencil H x 1 = pencil B x (1 - 1) from pencil_shift B x 1]
    simp [pencil]
  have hS := hclosure (Real.sqrt 2) (Real.sqrt_nonneg 2) (by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)])
  have hboost := doubledPolynomial_first_bound hH.positiveSemidefinite x
  rw [hone] at hboost
  have hcoeff := positive_border_coefficient_bound hA ha
  have hF := polynomial_real_eval_bound (rankPolynomial B x) (Real.sqrt 2 - 1)
    sqrt_two_offset_bound.1 sqrt_two_offset_bound.2
    (rankCoefficient_nonneg B x hB.positiveSemidefinite 1)
    (fun k hk => (hcoeff k (Nat.succ_le_iff.mpr hk)).1)
  rw [rankPolynomial_eval_real, rankPolynomial_coeff_zero,
    rankPolynomial_coeff_one] at hF
  rw [← pencil_shift B x (Real.sqrt 2)] at hF
  have hnonneg := hS.permanent_nonneg
  have hu : 0 ≤ B.permanent.re + (rankFirst B x).re := hnonneg.trans hF
  have hsq := (sq_le_sq₀ hnonneg hu).mpr hF
  have hper : (border a z B).permanent.re =
      a * (B.permanent.re + (rankFirst B x).re) := by
    rw [border_permanent_normalized a z B ha]
    simp only [x, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, zero_mul, sub_zero]
  calc
    (squaredEntries (border a z B)).permanent = a ^ 2 *
        ((hadamard B (conjugate B)).permanent.re +
          (rankFirst (hadamard B (conjugate B))
            (fun i => ((‖x i‖ ^ 2 : ℝ) : ℂ))).re) :=
      border_squared_permanent a z B ha
    _ ≤ a ^ 2 * (hadamard (pencil H x (Real.sqrt 2))
        (conjugate (pencil H x (Real.sqrt 2)))).permanent.re :=
      mul_le_mul_of_nonneg_left hboost (sq_nonneg a)
    _ = a ^ 2 * (squaredEntries (pencil H x (Real.sqrt 2))).permanent := by
      rw [permanent_hadamard_conjugate]
    _ ≤ a ^ 2 * (pencil H x (Real.sqrt 2)).permanent.re ^ 2 :=
      mul_le_mul_of_nonneg_left (hchild _ hS) (sq_nonneg a)
    _ ≤ a ^ 2 * (B.permanent.re + (rankFirst B x).re) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
    _ = (border a z B).permanent.re ^ 2 := by rw [hper]; ring

end ResearchMain.Chollet
