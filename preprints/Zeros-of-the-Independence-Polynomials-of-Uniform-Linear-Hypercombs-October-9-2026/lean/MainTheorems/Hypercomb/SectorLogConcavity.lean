import MainTheorems.Hypercomb.PolynomialFactors
import MainTheorems.Hypercomb.Unimodality

namespace ResearchMain.Hypercomb

open Polynomial

theorem sector_coefficients_positiveLC (p : ℝ[X]) (hp0 : p.coeff 0 = 1)
    (hp : RootsInLeftCone p) : ∃ e : ℕ, PositiveLC (coefficientSequence p) e := by
  suffices h : ∀ d : ℕ, ∀ p : ℝ[X], p.natDegree = d → p.coeff 0 = 1 →
      RootsInLeftCone p → ∃ e : ℕ, PositiveLC (coefficientSequence p) e from h _ p rfl hp0 hp
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro p hdegree hp0 hp
    by_cases hd : d = 0
    · have hconstant : p = 1 := by
        rw [eq_C_of_natDegree_eq_zero (hdegree.trans hd), hp0, map_one]
      rw [hconstant]
      exact ⟨0, coefficientSequence_one_positiveLC⟩
    · have hdegreepos : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (by omega)
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p (ne_of_gt hdegreepos)
      have hcone := hp z hz
      have hzne : z ≠ 0 := by intro he; subst z; simpa using hcone.1
      by_cases him : z.im = 0
      · have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
        have hrealroot : p.eval z.re = 0 := by
          rw [hzreal] at hz
          exact isRoot_of_aeval_algebraMap_eq_zero hz
        obtain ⟨q, hprod⟩ := (dvd_iff_isRoot.mpr hrealroot : (X - C z.re : ℝ[X]) ∣ p)
        have ht : (X - C z.re : ℝ[X]).coeff 0 ≠ 0 := by simpa using ne_of_lt hcone.1
        have hdeg : 0 < (X - C z.re : ℝ[X]).natDegree := by simp
        obtain ⟨hQ0, hPQ, hQdeg⟩ := normalized_factor_quotient hp0 hprod ht hdeg
        let Q := C ((X - C z.re : ℝ[X]).coeff 0) * q
        change Q.natDegree < p.natDegree at hQdeg
        have hPQ' : p = (1 + C (-z.re⁻¹) * X) * Q := by
          rw [normalize_linear hcone.1] at hPQ
          exact hPQ
        have hQsector := hp.of_factor hPQ'
        obtain ⟨e, he⟩ := ih Q.natDegree (by omega) Q rfl hQ0 hQsector
        have hb : 0 < -z.re⁻¹ := by
          have h := inv_pos.mpr (neg_pos.mpr hcone.1)
          simpa only [inv_neg] using h
        rw [hPQ', mul_comm]
        exact ⟨e + 1, he.coefficients_linear hb⟩
      · let P : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)
        obtain ⟨q, hprod⟩ := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz him
        have ht : P.coeff 0 ≠ 0 := by
          simp only [P, coeff_add, coeff_sub, coeff_X_pow, coeff_mul_X_zero, coeff_C_zero,
            ite_eq_right (by decide : ¬0 = 2), sub_zero, zero_add]
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hzne)
        have hcoeff : P.coeff 2 = 1 := by
          simp only [P, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
          norm_num
        have hdeg : 0 < P.natDegree := by
          have hle : 2 ≤ P.natDegree := le_natDegree_of_ne_zero (by rw [hcoeff]; norm_num)
          omega
        obtain ⟨hQ0, hPQ, hQdeg⟩ := normalized_factor_quotient hp0 hprod ht hdeg
        let Q := C (P.coeff 0) * q
        change Q.natDegree < p.natDegree at hQdeg
        let b := -2 * z.re / ‖z‖ ^ 2
        let c := (‖z‖ ^ 2)⁻¹
        have hPQ' : p = (1 + C b * X + C c * X ^ 2) * Q := by
          rw [normalize_quadratic hzne] at hPQ
          exact hPQ
        have hQsector := hp.of_factor hPQ'
        obtain ⟨e, he⟩ := ih Q.natDegree (by omega) Q rfl hQ0 hQsector
        have hnorm : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzne)
        have hb : 0 < b := div_pos (by nlinarith only [hcone.1]) hnorm
        have hc : 0 < c := inv_pos.mpr hnorm
        have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
          simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm z
        have hbc : c ≤ b ^ 2 := by
          dsimp only [b, c]
          rw [div_pow]
          apply (le_div_iff₀ (pow_pos hnorm 2)).mpr
          have heq : (‖z‖ ^ 2)⁻¹ * (‖z‖ ^ 2) ^ 2 = ‖z‖ ^ 2 := by field_simp
          rw [heq]
          nlinarith only [hsq, hcone.2]
        rw [hPQ', mul_comm]
        exact ⟨e + 2, he.coefficients_quadratic hb hc hbc⟩

theorem sector_coefficients_logConcave (p : ℝ[X]) (hp0 : p.coeff 0 = 1)
    (hp : RootsInLeftCone p) (k : ℤ) :
    coefficientSequence p (k - 1) * coefficientSequence p (k + 1) ≤ coefficientSequence p k ^ 2 := by
  obtain ⟨_, he⟩ := sector_coefficients_positiveLC p hp0 hp
  exact he.logConcave k

theorem sector_coefficients_unimodal (p : ℝ[X]) (hp0 : p.coeff 0 = 1)
    (hp : RootsInLeftCone p) : ∃ m : ℕ,
    (∀ k < m, coefficientSequence p k ≤ coefficientSequence p (k + 1)) ∧
    (∀ k ≥ m, coefficientSequence p (k + 1) ≤ coefficientSequence p k) := by
  obtain ⟨_, he⟩ := sector_coefficients_positiveLC p hp0 hp
  obtain ⟨m, _, hincr, hdecr⟩ := he.unimodal
  exact ⟨m, hincr, hdecr⟩

end ResearchMain.Hypercomb
