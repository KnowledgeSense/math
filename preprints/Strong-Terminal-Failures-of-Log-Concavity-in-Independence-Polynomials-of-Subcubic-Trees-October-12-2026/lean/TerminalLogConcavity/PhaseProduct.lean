import TerminalLogConcavity.RealCoefficientOrder
import TerminalLogConcavity.PhaseError

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

theorem phase_multiplier_bound {q : ℕ} (hq : 1 ≤ q) :
    (1 + 1 / (4 * (q : ℝ))) ^ q ≤ 2 := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have he : (q : ℝ) * (1 / (4 * (q : ℝ))) = 1 / 4 := by field_simp
  have h := power_error_le (by positivity : 0 ≤ 1 / (4 * (q : ℝ))) q (by rw [he]; norm_num)
  nlinarith

theorem natural_phase_scalar_bound {q : ℕ} (hq : 1 ≤ q) {p f : ℕ[X]}
    (h : ∀ j, 4 * q * p.coeff j ≤ (4 * q + 1) * f.coeff j) :
    RealCoeffLE (realPolynomial p) (C (1 + 1 / (4 * (q : ℝ))) * realPolynomial f) := by
  intro j
  rw [coeff_C_mul, realPolynomial_coeff, realPolynomial_coeff]
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hr : 4 * (q : ℝ) * p.coeff j ≤ (4 * (q : ℝ) + 1) * f.coeff j := by exact_mod_cast h j
  have he : 4 * (q : ℝ) * (1 + 1 / (4 * (q : ℝ))) = 4 * (q : ℝ) + 1 := by field_simp
  have hm := congrArg (fun z : ℝ => z * (f.coeff j : ℝ)) he
  nlinarith

theorem natural_phase_product_bound {q : ℕ} (hq : 1 ≤ q) (f g : ℕ → ℕ[X])
    (h : ∀ i < q, ∀ j, 4 * q * (f i).coeff j ≤ (4 * q + 1) * (g i).coeff j) :
    RealCoeffLE (realPolynomial (∏ i ∈ Finset.range q, f i))
      (C 2 * realPolynomial (∏ i ∈ Finset.range q, g i)) := by
  have hprod := RealCoeffLE.prod (Finset.range q)
    (fun i hi => natural_phase_scalar_bound hq (h i (Finset.mem_range.mp hi)))
    (fun i _ => realPolynomial_nonnegative (f i))
  have he : (∏ i ∈ Finset.range q, C (1 + 1 / (4 * (q : ℝ))) * realPolynomial (g i)) =
      C ((1 + 1 / (4 * (q : ℝ))) ^ q) * realPolynomial (∏ i ∈ Finset.range q, g i) := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← C_pow, realPolynomial, Polynomial.map_prod]
  have hf : (∏ i ∈ Finset.range q, realPolynomial (f i)) = realPolynomial (∏ i ∈ Finset.range q, f i) := by
    simp only [realPolynomial, Polynomial.map_prod]
  rw [he, hf] at hprod
  exact hprod.trans (RealCoeffLE.scale_mono (realPolynomial_nonnegative _) (phase_multiplier_bound hq))

end TerminalLogConcavity
