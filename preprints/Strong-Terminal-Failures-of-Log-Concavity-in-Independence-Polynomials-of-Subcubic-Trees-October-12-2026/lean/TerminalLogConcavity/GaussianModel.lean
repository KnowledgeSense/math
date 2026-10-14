import TerminalLogConcavity.BinomialPolynomial
import TerminalLogConcavity.BlockSum

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

noncomputable def gaussianFactor (q a lam i : ℕ) : ℕ[X] :=
  C (a ^ (i + 1) ^ 2) + (1 + C (lam * a ^ (2 * (i + 1))) * X) ^ q

noncomputable def gaussianPolynomial (q a lam : ℕ) : ℕ[X] :=
  ∏ i ∈ Finset.range q, gaussianFactor q a lam i

theorem gaussian_constant_lower (q a lam : ℕ) :
    a ^ squareSum q ≤ (gaussianPolynomial q a lam).coeff 0 := by
  have h : CoeffLE (∏ i ∈ Finset.range q, C (a ^ (i + 1) ^ 2))
      (gaussianPolynomial q a lam) := by
    apply CoeffLE.prod
    intro i _
    exact CoeffLE.le_add_right _ _
  have he : (∏ i ∈ Finset.range q, C (a ^ (i + 1) ^ 2) : ℕ[X]) = C (a ^ squareSum q) := by
    rw [← map_prod, Finset.prod_pow_eq_pow_sum]
    rfl
  rw [he] at h
  simpa only [coeff_C, ite_true] using h 0

theorem gaussian_coefficient_lower {q a lam j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ q) :
    q.choose j * lam ^ j * a ^ (squareSum q + j ^ 2) ≤
      (gaussianPolynomial q a lam).coeff j := by
  have hi : j - 1 ∈ Finset.range q := Finset.mem_range.mpr (by omega)
  let S := (Finset.range q).erase (j - 1)
  let e := ∑ i ∈ S, (i + 1) ^ 2
  have hjid : j - 1 + 1 = j := by omega
  have he : e + j ^ 2 = squareSum q := by
    have h := Finset.sum_erase_add (Finset.range q) (fun i => (i + 1) ^ 2) hi
    simpa [e, S, hjid, squareSum] using h
  have hconst : (∏ i ∈ S, C (a ^ (i + 1) ^ 2) : ℕ[X]) = C (a ^ e) := by
    rw [← map_prod, Finset.prod_pow_eq_pow_sum]
  have hothers : CoeffLE (C (a ^ e)) (∏ i ∈ S, gaussianFactor q a lam i) := by
    rw [← hconst]
    exact CoeffLE.prod (fun i _ => CoeffLE.le_add_right _ _)
  have hchosen : CoeffLE ((1 + C (lam * a ^ (2 * j)) * X : ℕ[X]) ^ q)
      (gaussianFactor q a lam (j - 1)) := by
    simpa [gaussianFactor, hjid, add_comm] using
      CoeffLE.le_add_right ((1 + C (lam * a ^ (2 * j)) * X : ℕ[X]) ^ q) (C (a ^ j ^ 2))
  have h := hothers.mul hchosen
  have hprod : (∏ i ∈ S, gaussianFactor q a lam i) * gaussianFactor q a lam (j - 1) =
      gaussianPolynomial q a lam := Finset.prod_erase_mul _ _ hi
  rw [hprod] at h
  have hcoeff := h j
  rw [coeff_C_mul, weighted_binomial_coeff, mul_pow, ← pow_mul] at hcoeff
  have he' : e + 2 * j * j = squareSum q + j ^ 2 := by nlinarith
  have hvalue : a ^ e * (q.choose j * (lam ^ j * a ^ (2 * j * j))) =
      q.choose j * lam ^ j * a ^ (squareSum q + j ^ 2) := by
    calc
      _ = q.choose j * lam ^ j * (a ^ e * a ^ (2 * j * j)) := by ring
      _ = _ := by rw [← pow_add, he']
  rwa [hvalue] at hcoeff

end TerminalLogConcavity
