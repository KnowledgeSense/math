import OscillatoryRecurrence.OriginalRecurrence

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

/-- The family is independent of the frequency and has the source's normalization. -/
theorem uniform_monic_family :
    (∀ j, (recurrenceFamily j).Monic ∧ (recurrenceFamily j).natDegree=j) ∧
      recurrenceFamily 0=1 ∧ recurrenceFamily 1=X-C 2 := by
  exact ⟨fun j => ⟨recurrenceFamily_monic j,recurrenceFamily_natDegree j⟩,
    recurrenceFamily_zero,recurrenceFamily_one⟩

theorem orthogonalPolynomial_zero (η : ℝ) : orthogonalPolynomial η 0=1 := by
  simp [orthogonalPolynomial]

theorem alpha_zero (η : ℝ) : alpha η 0=2/η := by
  have hJ : polynomialBorder 1=C 4 := by
    change (Matrix.of (fun a b : Fin 1 => endpointMoment (a.val+borderColumn 1 b))).det=C 4
    rw [Matrix.det_fin_one]
    norm_num [endpointMoment,borderColumn]
    norm_num only [map_ofNat]
  simp only [alpha,realBorder,realHankel,Nat.zero_add,hJ,polynomialHankel_one]
  norm_num [polynomialBorder]

theorem original_initial_recurrence (m : ℤ) (hm : m≠0) :
    X*orthogonalPolynomial ((m:ℝ)*Real.pi) 0 =
      orthogonalPolynomial ((m:ℝ)*Real.pi) 1+
      C (Complex.I*(alpha ((m:ℝ)*Real.pi) 0:ℂ))*orthogonalPolynomial ((m:ℝ)*Real.pi) 0 := by
  rw [orthogonalPolynomial_zero,mul_one,mul_one,
    (orthogonalPolynomial_monic _ 1).eq_X_add_C (orthogonalPolynomial_natDegree _ 1)]
  have hc := subleading_border_ratio m hm 0
  change (orthogonalPolynomial ((m:ℝ)*Real.pi) 1).coeff 0 = _ at hc
  rw [neg_div,border_ratio_normalization m hm 1 (by omega)] at hc
  have ht : ((((m:ℝ)*Real.pi):ℂ))≠0 := by
    exact_mod_cast mul_ne_zero (Int.cast_ne_zero.mpr hm) Real.pi_ne_zero
  have hh := evaluatedHankel_ne_zero m hm 1
  have hb0 : evaluatedBorder ((m:ℝ)*Real.pi) 0=0 := by
    simp [evaluatedBorder,polynomialBorder]
  have he : -( -evaluatedBorder ((m:ℝ)*Real.pi) 1 /
      ((Complex.I*((m:ℝ)*Real.pi))*evaluatedHankel ((m:ℝ)*Real.pi) 1))+
      Complex.I*(alpha ((m:ℝ)*Real.pi) 0:ℂ)=0 := by
    simp only [alpha,Complex.ofReal_div,Complex.ofReal_sub,realBorder_cast,
      realHankel_cast,zero_add,hb0,zero_div,sub_zero]
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring
  rw [hc,add_assoc,← map_add,he,map_zero,add_zero]

/-- Existence, exact degree and literal integral orthogonality of the source polynomials. -/
theorem original_orthogonal_family (m : ℤ) (hm : m≠0) (n : ℕ) :
    (orthogonalPolynomial ((m:ℝ)*Real.pi) n).Monic ∧
      (orthogonalPolynomial ((m:ℝ)*Real.pi) n).natDegree=n ∧
      (∀ k<n, ∫ x : ℝ in (-1)..1,
        (x:ℂ)^k*(orthogonalPolynomial ((m:ℝ)*Real.pi) n).eval (x:ℂ)*
          (x:ℂ)*Complex.exp (Complex.I*((m:ℝ)*Real.pi)*x)=0) := by
  refine ⟨orthogonalPolynomial_monic _ _,orthogonalPolynomial_natDegree _ _,?_⟩
  intro k hk
  simpa only [pow_add,pow_one,mul_assoc,mul_comm,mul_left_comm] using
    orthogonalPolynomial_integral_zero m hm n k hk

end OscillatoryRecurrence
