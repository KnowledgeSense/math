import CircleResidues.Definitions

noncomputable section
open PowerSeries Finset
namespace CircleResidues

/-- Ordinary partial Bell polynomial, with the ordinary (not exponential) coefficient convention. -/
def ordinaryBell (j ell : ℕ) : ℚ :=
  coeff j ((mk sourceCoefficient : PowerSeries ℚ) ^ ell)

/-- The formal exponential definition agrees with the source's finite ordinary-Bell formula. -/
theorem residuePolynomial_eq_bell_sum (t : ℚ) (j : ℕ) :
    residuePolynomial t j = ∑ ell ∈ range (j + 1),
      (-t) ^ ell / (ell.factorial : ℚ) * ordinaryBell j ell := by
  let S : PowerSeries ℚ := mk sourceCoefficient
  have hS0 : constantCoeff S = 0 := by simp [S, constantCoeff_mk]
  have hS : (X : PowerSeries ℚ) ∣ S := X_dvd_iff.mpr hS0
  have hexp : (mk fun k => -t * sourceCoefficient k) = C (-t) * S := by
    ext k
    simp [S, coeff_C_mul]
  have hC0 : constantCoeff (C (-t) * S) = 0 := by simp [hS0]
  rw [residuePolynomial, hexp, coeff_subst' (HasSubst.of_constantCoeff_zero' hC0)]
  rw [finsum_eq_sum_of_support_subset _ (s := range (j + 1)) (by
    intro ell hell
    by_contra hout
    have hjl : j < ell := by
      have hout' : ¬ ell < j + 1 := by simpa using hout
      omega
    have hzero : coeff j ((C (-t) * S) ^ ell) = 0 := by
      apply X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (dvd_mul_of_dvd_right hS (C (-t))) ell) j hjl
    exact hell (by dsimp only; rw [hzero, smul_zero]))]
  apply sum_congr rfl
  intro ell hell
  simp only [coeff_exp, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul, mul_pow, ← map_pow,
    coeff_C_mul, ordinaryBell, S]
  ring

end CircleResidues
