import MainTheorems.DiagonalSchatten.RayContacts
import MainTheorems.DiagonalSchatten.StationaryQuarticContacts

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Polynomial

variable {J : Type*} [Fintype J]

def interiorSlopes (X : Matrix (Fin 2) J ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.filter fun j => 0 < X 0 j ∧ 0 < X 1 j).image
    (fun j => X 1 j / X 0 j)

def firstAxisPresent (X : Matrix (Fin 2) J ℝ) : Prop :=
  ∃ j, 0 < X 0 j ∧ X 1 j = 0

def secondAxisPresent (X : Matrix (Fin 2) J ℝ) : Prop :=
  ∃ j, X 0 j = 0 ∧ 0 < X 1 j

def raySupportCard (X : Matrix (Fin 2) J ℝ) : ℕ := by
  classical
  exact (interiorSlopes X).card + (if firstAxisPresent X then 1 else 0) +
    (if secondAxisPresent X then 1 else 0)

namespace RayParameters

variable (g : RayParameters)

theorem stationary_support_classification (s : ℝ) (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0)
    (q : Fin 3 → ℝ)
    (hs : fderiv ℝ (faceObjective (fun x => s * g.functional x) X) (facePoint X) =
      ∑ i, q i • fderiv ℝ (faceGram X i) (facePoint X))
    (hp : g.contactPolynomial s q ≠ 0) :
    raySupportCard X ≤ 2 ∨
      ((interiorSlopes X).card = 1 ∧ firstAxisPresent X ∧ secondAxisPresent X) := by
  classical
  have hroots : ∀ r ∈ interiorSlopes X, 0 < r ∧
      (g.contactPolynomial s q).eval r = 0 ∧
      (g.contactPolynomial s q).derivative.eval r = 0 := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    have hjp := (Finset.mem_filter.mp hj).2
    exact ⟨div_pos hjp.2 hjp.1, g.interior_stationary_contact s X hX hD q hs j hjp.1 hjp.2⟩
  have hfirst : firstAxisPresent X → (g.contactPolynomial s q).eval 0 = 0 := by
    rintro ⟨j, hj0, hj1⟩
    exact g.first_axis_contact s X hX hD q hs j hj0 hj1
  have hsecond : secondAxisPresent X → (g.contactPolynomial s q).natDegree < 4 := by
    rintro ⟨j, hj0, hj1⟩
    exact g.second_axis_contact s X hX hD q hs j hj0 hj1
  have hboundFirst : (if firstAxisPresent X then 1 else 0) ≤
      (if (g.contactPolynomial s q).eval 0 = 0 then 1 else 0) := by
    split_ifs with hF hP <;> first | omega | exact (hP (hfirst hF)).elim
  have hboundSecond : (if secondAxisPresent X then 1 else 0) ≤
      (if (g.contactPolynomial s q).natDegree < 4 then 1 else 0) := by
    split_ifs with hF hP <;> first | omega | exact (hP (hsecond hF)).elim
  rcases stationary_quartic_classification hp (g.contactPolynomial_degree s q)
      (interiorSlopes X) hroots with htwo | hthree
  · left
    unfold raySupportCard
    omega
  · by_cases hF : firstAxisPresent X
    · by_cases hS : secondAxisPresent X
      · exact Or.inr ⟨hthree.1, hF, hS⟩
      · left
        simp [raySupportCard, hthree.1, hF, hS]
    · left
      unfold raySupportCard
      simp only [hthree.1, hF, ite_false, add_zero]
      split_ifs <;> omega

theorem zero_contactPolynomial_functional (s : ℝ) (q : Fin 3 → ℝ)
    (hp : g.contactPolynomial s q = 0)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0)
    (x : Fin 2 → ℝ) (hx0 : 0 ≤ x 0) (hx1 : 0 ≤ x 1) :
    s * g.functional x = q 0 * x 0 ^ 2 + q 1 * x 1 ^ 2 + q 2 * x 0 * x 1 := by
  by_cases hx0z : x 0 = 0
  · by_cases hx1z : x 1 = 0
    · have hx : x = 0 := by funext i; fin_cases i <;> simp [hx0z, hx1z]
      simp [hx, functional, numerator, denominator, image]
    · have he := congrArg (fun P : ℝ[X] => P.coeff 4) hp
      rw [g.contactPolynomial_coeff_four, Polynomial.coeff_zero] at he
      have hDs := hD (![0, 1] : Fin 2 → ℝ) (by simp) (by simp) (Or.inr (by simp))
      have hv : s * g.functional ![0, 1] = q 1 := by
        rw [functional, ← mul_div_assoc]
        apply (div_eq_iff hDs).mpr
        simp only [numerator, denominator, image, Matrix.cons_val_zero, Matrix.cons_val_one,
          zero_pow (by decide : 2 ≠ 0), one_pow, mul_zero, zero_mul, mul_one,
          add_zero, zero_add]
        nlinarith [he]
      have hx : x = x 1 • (![0, 1] : Fin 2 → ℝ) := by
        funext i
        fin_cases i <;> simp [hx0z]
      rw [hx, g.signed_functional_homogeneous, hv]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        mul_zero, mul_one, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add, add_zero]
      ring
  · have hx0p : 0 < x 0 := lt_of_le_of_ne hx0 (Ne.symm hx0z)
    let r := x 1 / x 0
    have hr : 0 ≤ r := div_nonneg hx1 hx0p.le
    have hDn := hD (![1, r] : Fin 2 → ℝ) (by simp) (by simpa using hr)
      (Or.inl (by simp))
    have he := congrArg (fun P : ℝ[X] => P.eval r) hp
    simp only [contactPolynomial, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_zero] at he
    have hv : s * g.functional ![1, r] = (rayQuadraticPolynomial q).eval r := by
      rw [g.functional_polynomial_quotient]
      apply (div_eq_iff (by simpa only [g.denominatorPolynomial_eval] using hDn)).mpr
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      linarith [he]
    have hx : x = x 0 • (![1, r] : Fin 2 → ℝ) := by
      funext i
      fin_cases i
      · simp
      · change x 1 = x 0 * (x 1 / x 0)
        field_simp [hx0z]
    rw [hx, g.signed_functional_homogeneous, hv, rayQuadraticPolynomial_eval]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    ring

theorem zero_contactPolynomial_objective (s : ℝ) (q : Fin 3 → ℝ)
    (hp : g.contactPolynomial s q = 0)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0)
    (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j) :
    columnObjective (fun x => s * g.functional x) X =
      q 0 * gramFirst X + q 1 * gramSecond X + q 2 * gramCross X := by
  calc
    _ = ∑ j, (q 0 * X 0 j ^ 2 + q 1 * X 1 j ^ 2 + q 2 * X 0 j * X 1 j) := by
      unfold columnObjective
      apply Finset.sum_congr rfl
      intro j _
      exact g.zero_contactPolynomial_functional s q hp hD (fun i => X i j) (hX 0 j) (hX 1 j)
    _ = _ := by
      unfold gramFirst gramSecond gramCross
      simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

end RayParameters

end

end ResearchMain.DiagonalSchatten
