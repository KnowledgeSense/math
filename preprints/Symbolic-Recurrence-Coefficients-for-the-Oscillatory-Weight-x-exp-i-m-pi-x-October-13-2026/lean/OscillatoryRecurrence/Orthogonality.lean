import OscillatoryRecurrence.Nonvanishing
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open scoped BigOperators Matrix
open Polynomial
namespace OscillatoryRecurrence

/-- The moment functional applied after multiplication by a monomial. -/
def momentFunctional (η : ℝ) (k : ℕ) : ℂ[X] →ₗ[ℂ] ℂ :=
  Polynomial.lsum (fun j => LinearMap.mulRight ℂ (moment η (k+j)))

@[simp] theorem momentFunctional_monomial (η : ℝ) (k j : ℕ) (c : ℂ) :
    momentFunctional η k (monomial j c) = c * moment η (k+j) := by
  simp [momentFunctional, Polynomial.lsum_apply]

@[simp] theorem momentFunctional_X_pow (η : ℝ) (k j : ℕ) :
    momentFunctional η k (X^j) = moment η (k+j) := by
  simpa only [Polynomial.monomial_one_right_eq_X_pow, one_mul] using
    momentFunctional_monomial η k j 1

 def momentMatrix (η : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => moment η (a.val+b.val)

 def lowerCoefficients (η : ℝ) (n : ℕ) : Fin n → ℂ :=
  (momentMatrix η n)⁻¹ *ᵥ (fun a => -moment η (a.val+n))

 def orthogonalPolynomial (η : ℝ) (n : ℕ) : ℂ[X] :=
  X^n + ∑ j : Fin n, monomial j.val (lowerCoefficients η n j)

 theorem lowerCoefficients_equation (m : ℤ) (hm : m ≠ 0) (n : ℕ) (a : Fin n) :
    ∑ j : Fin n, moment ((m:ℝ)*Real.pi) (a.val+j.val) *
      lowerCoefficients ((m:ℝ)*Real.pi) n j =
      -moment ((m:ℝ)*Real.pi) (a.val+n) := by
  have hdet : IsUnit (momentMatrix ((m:ℝ)*Real.pi) n).det := by
    exact isUnit_iff_ne_zero.mpr (hankel_ne_zero m hm n)
  have h := Matrix.mul_nonsing_inv (momentMatrix ((m:ℝ)*Real.pi) n) hdet
  change ((momentMatrix ((m:ℝ)*Real.pi) n).mulVec
    ((momentMatrix ((m:ℝ)*Real.pi) n)⁻¹.mulVec
      (fun a : Fin n => -moment ((m:ℝ)*Real.pi) (a.val+n)))) a = _
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]


 theorem orthogonalPolynomial_orthogonal (m : ℤ) (hm : m ≠ 0)
    (n k : ℕ) (hk : k<n) :
    momentFunctional ((m:ℝ)*Real.pi) k
      (orthogonalPolynomial ((m:ℝ)*Real.pi) n) = 0 := by
  simp only [orthogonalPolynomial, map_add, map_sum,
    momentFunctional_X_pow, momentFunctional_monomial]
  have he := lowerCoefficients_equation m hm n ⟨k,hk⟩
  simp only at he
  simpa only [mul_comm, he, add_neg_cancel] using
    (show moment ((m:ℝ)*Real.pi) (k+n) +
      ∑ j : Fin n, moment ((m:ℝ)*Real.pi) (k+j.val) *
        lowerCoefficients ((m:ℝ)*Real.pi) n j = 0 by rw [he,add_neg_cancel])

 theorem orthogonalPolynomial_coeff_leading (η : ℝ) (n : ℕ) :
    (orthogonalPolynomial η n).coeff n = 1 := by
  simp [orthogonalPolynomial, Polynomial.coeff_monomial, ne_of_lt (Fin.is_lt _)]

 theorem orthogonalPolynomial_natDegree_le (η : ℝ) (n : ℕ) :
    (orthogonalPolynomial η n).natDegree ≤ n := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact Polynomial.natDegree_X_pow_le n
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact le_trans (Polynomial.natDegree_monomial_le _) (Nat.le_of_lt j.is_lt)

 theorem orthogonalPolynomial_monic (η : ℝ) (n : ℕ) :
    (orthogonalPolynomial η n).Monic := by
  exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
    (orthogonalPolynomial_natDegree_le η n) (orthogonalPolynomial_coeff_leading η n)

 theorem orthogonalPolynomial_natDegree (η : ℝ) (n : ℕ) :
    (orthogonalPolynomial η n).natDegree = n := by
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (orthogonalPolynomial_natDegree_le η n)
    (by rw [orthogonalPolynomial_coeff_leading]; exact one_ne_zero)

theorem polynomial_integrable (η : ℝ) (k : ℕ) (p : ℂ[X]) :
    IntervalIntegrable (fun x : ℝ => p.eval (x:ℂ) * (x:ℂ)^(k+1) *
      Complex.exp (Complex.I*η*x)) MeasureTheory.volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- The finite moment functional is the original oscillatory integral. -/
theorem momentFunctional_integral (η : ℝ) (k : ℕ) (p : ℂ[X]) :
    momentFunctional η k p = ∫ x : ℝ in (-1)..1,
      p.eval (x:ℂ) * (x:ℂ)^(k+1) * Complex.exp (Complex.I*η*x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      simp only [Polynomial.eval_add, add_mul]
      rw [intervalIntegral.integral_add (polynomial_integrable η k p)
        (polynomial_integrable η k q)]
  | monomial j c =>
      rw [momentFunctional_monomial]
      simp only [Polynomial.eval_monomial, moment, exponentialMoment]
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext x
      simp only [pow_add, pow_one]
      ring

 theorem orthogonalPolynomial_integral_zero (m : ℤ) (hm : m ≠ 0)
    (n k : ℕ) (hk : k<n) :
    (∫ x : ℝ in (-1)..1,
      (orthogonalPolynomial ((m:ℝ)*Real.pi) n).eval (x:ℂ) *
      (x:ℂ)^(k+1) * Complex.exp (Complex.I*((m:ℝ)*Real.pi)*x)) = 0 := by
  have h := orthogonalPolynomial_orthogonal m hm n k hk
  rw [momentFunctional_integral] at h
  simpa only [Complex.ofReal_mul] using h

theorem zero_of_moments_zero (m : ℤ) (hm : m ≠ 0) (n : ℕ) (p : ℂ[X])
    (hp : p.degree < n)
    (horth : ∀ k : Fin n, momentFunctional ((m:ℝ)*Real.pi) k.val p = 0) :
    p = 0 := by
  have hs : p = ∑ j : Fin n, monomial j.val (p.coeff j.val) := by
    exact ((Polynomial.sum_fin (fun j c : _ => monomial j c)
      (fun j => Polynomial.monomial_zero_right j) hp).trans
      (Polynomial.sum_monomial_eq p)).symm
  have he : (momentMatrix ((m:ℝ)*Real.pi) n).mulVec
      (fun j : Fin n => p.coeff j.val) = 0 := by
    funext k
    have h := horth k
    conv_lhs at h => rw [hs]
    simp only [map_sum, momentFunctional_monomial] at h
    simpa only [Matrix.mulVec, dotProduct, momentMatrix, mul_comm,
      Pi.zero_apply] using h
  have hu : IsUnit (momentMatrix ((m:ℝ)*Real.pi) n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (hankel_ne_zero m hm n))
  have hz : (fun j : Fin n => p.coeff j.val) = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hu) (by simpa using he)
  rw [hs]
  apply Finset.sum_eq_zero
  intro j hj
  have hc := congrFun hz j
  simp only [Pi.zero_apply] at hc
  rw [hc, Polynomial.monomial_zero_right]

 theorem orthogonalPolynomial_unique (m : ℤ) (hm : m ≠ 0) (n : ℕ) (p : ℂ[X])
    (hdegree : p.natDegree ≤ n) (hlead : p.coeff n = 1)
    (horth : ∀ k : ℕ, k<n → momentFunctional ((m:ℝ)*Real.pi) k p = 0) :
    p = orthogonalPolynomial ((m:ℝ)*Real.pi) n := by
  apply sub_eq_zero.mp
  apply zero_of_moments_zero m hm n
  · rw [Polynomial.degree_lt_iff_coeff_zero]
    intro j hj
    rw [Polynomial.coeff_sub]
    rcases eq_or_lt_of_le hj with he | he
    · subst j
      rw [hlead, orthogonalPolynomial_coeff_leading, sub_self]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree he),
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (orthogonalPolynomial_natDegree_le _ n) he), sub_self]
  · intro k
    rw [map_sub, horth k.val k.is_lt,
      orthogonalPolynomial_orthogonal m hm n k.val k.is_lt, sub_self]

 theorem momentFunctional_shift (η : ℝ) (k j : ℕ) (p : ℂ[X]) :
    momentFunctional η k (X^j*p) = momentFunctional η (k+j) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add,map_add,hp,hq]
  | monomial a c =>
      rw [Polynomial.X_pow_mul_monomial]
      simp only [momentFunctional_monomial]
      congr 2
      omega

/-- The bilinear squared norm; positivity is neither assumed nor required. -/
def squaredNorm (η : ℝ) (n : ℕ) : ℂ :=
  momentFunctional η n (orthogonalPolynomial η n)

 theorem squaredNorm_ne_zero (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    squaredNorm ((m:ℝ)*Real.pi) n ≠ 0 := by
  intro hz
  have hp := zero_of_moments_zero m hm (n+1)
    (orthogonalPolynomial ((m:ℝ)*Real.pi) n)
    (by rw [Polynomial.degree_eq_natDegree (orthogonalPolynomial_monic _ n).ne_zero,
      orthogonalPolynomial_natDegree]; exact_mod_cast Nat.lt_succ_self n)
    (by
      intro k
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ k.is_lt) with hk | hk
      · exact orthogonalPolynomial_orthogonal m hm n k.val hk
      · simpa only [hk, squaredNorm] using hz)
  exact (orthogonalPolynomial_monic _ n).ne_zero hp

 theorem momentFunctional_monomial_mul (η : ℝ) (k j : ℕ) (c : ℂ) (p : ℂ[X]) :
    momentFunctional η k (monomial j c*p) = c*momentFunctional η (k+j) p := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
    ← Polynomial.smul_eq_C_mul, map_smul, momentFunctional_shift, smul_eq_mul]

 theorem orthogonalPolynomial_pairing_zero (m : ℤ) (hm : m ≠ 0)
    (n : ℕ) (q : ℂ[X]) (hq : q.degree < n) :
    momentFunctional ((m:ℝ)*Real.pi) 0
      (q * orthogonalPolynomial ((m:ℝ)*Real.pi) n) = 0 := by
  have hs : q = ∑ j : Fin n, monomial j.val (q.coeff j.val) :=
    ((Polynomial.sum_fin (fun j c : _ => monomial j c)
      (fun j => Polynomial.monomial_zero_right j) hq).trans
      (Polynomial.sum_monomial_eq q)).symm
  rw [hs, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [momentFunctional_monomial_mul, zero_add,
    orthogonalPolynomial_orthogonal m hm n j.val j.is_lt, mul_zero]

 theorem squaredNorm_pairing (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    momentFunctional ((m:ℝ)*Real.pi) 0
      (orthogonalPolynomial ((m:ℝ)*Real.pi) n *
        orthogonalPolynomial ((m:ℝ)*Real.pi) n) =
      squaredNorm ((m:ℝ)*Real.pi) n := by
  change momentFunctional ((m:ℝ)*Real.pi) 0
    ((X^n + ∑ j : Fin n, monomial j.val
      (lowerCoefficients ((m:ℝ)*Real.pi) n j))*
      orthogonalPolynomial ((m:ℝ)*Real.pi) n) = _
  rw [add_mul, map_add, momentFunctional_shift, zero_add,
    Finset.sum_mul, map_sum]
  have hz : (∑ j : Fin n, momentFunctional ((m:ℝ)*Real.pi) 0
      (monomial j.val (lowerCoefficients ((m:ℝ)*Real.pi) n j)*
        orthogonalPolynomial ((m:ℝ)*Real.pi) n)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [momentFunctional_monomial_mul, zero_add,
      orthogonalPolynomial_orthogonal m hm n j.val j.is_lt, mul_zero]
  rw [hz,add_zero]
  rfl

end OscillatoryRecurrence
