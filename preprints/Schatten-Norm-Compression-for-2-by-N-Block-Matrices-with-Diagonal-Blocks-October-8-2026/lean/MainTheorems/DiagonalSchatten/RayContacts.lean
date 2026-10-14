import MainTheorems.DiagonalSchatten.RayExtremizer
import MainTheorems.DiagonalSchatten.RayPolynomials
import MainTheorems.DiagonalSchatten.FacePartial
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

namespace RayParameters

variable (g : RayParameters) {J : Type*} [Fintype J]

theorem signed_functional_homogeneous (s : ℝ) (x : Fin 2 → ℝ) (t : ℝ) :
    s * g.functional (t • x) = t ^ 2 * (s * g.functional x) := by
  rw [g.functional_homogeneous]
  ring

theorem interior_stationary_contact (s : ℝ) (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0)
    (q : Fin 3 → ℝ)
    (hs : fderiv ℝ (faceObjective (fun x => s * g.functional x) X) (facePoint X) =
      ∑ i, q i • fderiv ℝ (faceGram X i) (facePoint X))
    (j : J) (hj0 : 0 < X 0 j) (hj1 : 0 < X 1 j) :
    (g.contactPolynomial s q).eval (X 1 j / X 0 j) = 0 ∧
      (g.contactPolynomial s q).derivative.eval (X 1 j / X 0 j) = 0 := by
  let r := X 1 j / X 0 j
  let x : Fin 2 → ℝ := ![1, r]
  let h : (Fin 2 → ℝ) → ℝ := fun y => s * g.functional y
  have hr : 0 < r := div_pos hj1 hj0
  have hcol : (fun i => X i j) = X 0 j • x := by
    funext i
    fin_cases i
    · simp [x]
    · change X 1 j = X 0 j * (X 1 j / X 0 j)
      field_simp [hj0.ne']
  have hrow : X 1 j = X 0 j * r := by
    dsimp [r]
    field_simp [hj0.ne']
  have hΦ : DifferentiableAt ℝ (faceObjective h X) (facePoint X) :=
    (g.signed_faceObjective_contDiffAt (n := 1) X hX hD s).differentiableAt (by norm_num)
  have hxD : g.denominator x ≠ 0 := hD x (by simp [x]) (by simpa [x] using hr.le)
    (Or.inl (by simp [x]))
  have hcolD : g.denominator (fun i => X i j) ≠ 0 :=
    hD _ (hX 0 j) (hX 1 j) (Or.inl hj0)
  have hdx : DifferentiableAt ℝ h x :=
    (contDiffAt_const.mul (g.contDiffAt_functional (n := 1) x hxD)).differentiableAt (by norm_num)
  have hdc : DifferentiableAt ℝ h (fun i => X i j) :=
    (contDiffAt_const.mul (g.contDiffAt_functional (n := 1) _ hcolD)).differentiableAt (by norm_num)
  have hhom (y : Fin 2 → ℝ) (t : ℝ) : h (t • y) = t ^ 2 * h y :=
    g.signed_functional_homogeneous s y t
  have hvcol := faceObjective_value_contact X hX hhom hΦ q hs j
  have hv : h x = (rayQuadraticPolynomial q).eval r := by
    rw [hcol, hhom] at hvcol
    rw [hrow] at hvcol
    have hm : X 0 j ^ 2 * (h x - (rayQuadraticPolynomial q).eval r) = 0 := by
      rw [rayQuadraticPolynomial_eval]
      nlinarith [hvcol]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (pow_ne_zero 2 hj0.ne'))
  have hp := faceObjective_second_contact X hX j hj1 hΦ hdc q hs
  have hscale := quadratic_homogeneous_derivative_scale x (Pi.single 1 1) (X 0 j)
    hdx (hcol ▸ hdc) (fun y => hhom y (X 0 j))
  rw [← hcol, map_smul, smul_eq_mul, hp, hrow] at hscale
  have hslope : fderiv ℝ h x (Pi.single 1 1) = 2 * q 1 * r + q 2 := by
    have hm : X 0 j ^ 2 * (fderiv ℝ h x (Pi.single 1 1) - (2 * q 1 * r + q 2)) = 0 := by
      nlinarith [hscale]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (pow_ne_zero 2 hj0.ne'))
  have hcurve : HasDerivAt (fun t : ℝ => (![1, t] : Fin 2 → ℝ)) (Pi.single 1 1) r := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! hasDerivAt_const r (1 : ℝ) using 1
    · convert! hasDerivAt_id r using 1
  have hd : HasDerivAt (fun t : ℝ => h ![1, t]) (fderiv ℝ h x (Pi.single 1 1)) r := by
    convert! hdx.hasFDerivAt.comp_hasDerivAt_of_eq r hcurve (by rfl) using 1
  rw [hslope, ← rayQuadraticPolynomial_derivative_eval] at hd
  exact g.contactPolynomial_of_quotient_match s q r hxD hv hd

theorem first_axis_contact (s : ℝ) (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0)
    (q : Fin 3 → ℝ)
    (hs : fderiv ℝ (faceObjective (fun x => s * g.functional x) X) (facePoint X) =
      ∑ i, q i • fderiv ℝ (faceGram X i) (facePoint X))
    (j : J) (hj0 : 0 < X 0 j) (hj1 : X 1 j = 0) :
    (g.contactPolynomial s q).eval 0 = 0 := by
  have hΦ := (g.signed_faceObjective_contDiffAt (n := 1) X hX hD s).differentiableAt
    (by norm_num)
  have hc := faceObjective_value_contact X hX (g.signed_functional_homogeneous s) hΦ q hs j
  have hcol : (fun i => X i j) = X 0 j • (![1, 0] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;> simp [hj1]
  rw [hcol, g.signed_functional_homogeneous] at hc
  have hunit : s * g.functional ![1, 0] = q 0 := by
    have he : X 0 j ^ 2 * (s * g.functional ![1, 0] - q 0) = 0 := by
      simp only [hj1, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hc
      nlinarith [hc]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hj0.ne'))
  have hD0 := hD (![1, 0] : Fin 2 → ℝ) (by simp) (by simp) (Or.inl (by simp))
  rw [g.functional_polynomial_quotient] at hunit
  have he := (div_eq_iff (by simpa only [g.denominatorPolynomial_eval] using hD0)).mp hunit
  rw [contactPolynomial, Polynomial.eval_sub]
  apply sub_eq_zero.mpr
  calc
    (rayQuadraticPolynomial q * g.denominatorPolynomial).eval 0 =
        q 0 * g.denominatorPolynomial.eval 0 := by
      rw [Polynomial.eval_mul, rayQuadraticPolynomial_eval]
      ring
    _ = (Polynomial.C s * g.numeratorPolynomial).eval 0 := he.symm

theorem second_axis_contact (s : ℝ) (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0)
    (q : Fin 3 → ℝ)
    (hs : fderiv ℝ (faceObjective (fun x => s * g.functional x) X) (facePoint X) =
      ∑ i, q i • fderiv ℝ (faceGram X i) (facePoint X))
    (j : J) (hj0 : X 0 j = 0) (hj1 : 0 < X 1 j) :
    (g.contactPolynomial s q).natDegree < 4 := by
  have hΦ := (g.signed_faceObjective_contDiffAt (n := 1) X hX hD s).differentiableAt
    (by norm_num)
  have hc := faceObjective_value_contact X hX (g.signed_functional_homogeneous s) hΦ q hs j
  have hcol : (fun i => X i j) = X 1 j • (![0, 1] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;> simp [hj0]
  rw [hcol, g.signed_functional_homogeneous] at hc
  have hunit : s * g.functional ![0, 1] = q 1 := by
    have he : X 1 j ^ 2 * (s * g.functional ![0, 1] - q 1) = 0 := by
      simp only [hj0, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, zero_add,
        add_zero] at hc
      nlinarith [hc]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hj1.ne'))
  have hDs := hD (![0, 1] : Fin 2 → ℝ) (by simp) (by simp) (Or.inr (by simp))
  rw [functional, ← mul_div_assoc] at hunit
  have he := (div_eq_iff hDs).mp hunit
  have hcoeff : (g.contactPolynomial s q).coeff 4 = 0 := by
    rw [g.contactPolynomial_coeff_four]
    simp only [numerator, denominator, image, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_pow (by decide : 2 ≠ 0), one_pow, mul_zero, zero_mul, mul_one,
      add_zero, zero_add] at he
    nlinarith [he]
  have hdeg := Polynomial.natDegree_le_pred (g.contactPolynomial_degree s q) hcoeff
  omega

end RayParameters

end

end ResearchMain.DiagonalSchatten
