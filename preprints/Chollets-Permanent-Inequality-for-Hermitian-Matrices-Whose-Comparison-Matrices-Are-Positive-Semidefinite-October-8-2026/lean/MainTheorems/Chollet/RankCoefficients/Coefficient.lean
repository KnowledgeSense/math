import MainTheorems.Chollet.RankCoefficients.SquareFree
import Mathlib.Algebra.BigOperators.Finsupp.Basic

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

open MvPolynomial

variable {I : Type*} [DecidableEq I]

def exponent (s : Finset I) : I →₀ ℕ := ∑ i ∈ s, Finsupp.single i 1

theorem exponent_apply (s : Finset I) (i : I) : exponent s i = if i ∈ s then 1 else 0 := by
  simp [exponent, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem exponent_le_one (s : Finset I) (i : I) : exponent s i ≤ 1 := by
  rw [exponent_apply]
  split_ifs <;> omega

theorem squareIdeal_coeff_zero (p : MvPolynomial I ℂ) (hp : p ∈ squareIdeal I)
    (d : I →₀ ℕ) (hd : ∀ i, d i ≤ 1) : p.coeff d = 0 := by
  have h : ∀ q : MvPolynomial I ℂ, q ∈ squareIdeal I →
      ∀ e : I →₀ ℕ, (∀ i, e i ≤ 1) → q.coeff e = 0 := by
    intro q hq
    change q ∈ Submodule.span (MvPolynomial I ℂ)
      (Set.range fun i : I => (X i : MvPolynomial I ℂ) ^ 2) at hq
    induction hq using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      intro e he
      change (X i ^ 2 : MvPolynomial I ℂ).coeff e = 0
      rw [X_pow_eq_monomial, coeff_monomial]
      split_ifs with hEq
      · have h₁ := he i
        rw [← hEq, Finsupp.single_eq_same] at h₁
        omega
      · rfl
    | zero => intro e _; simp
    | add p q _ _ ihp ihq =>
      intro e he
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ihp e he, ihq e he, add_zero]
    | smul q p _ ih =>
      intro e he
      change (q * p).coeff e = 0
      rw [coeff_mul]
      apply Finset.sum_eq_zero
      intro ab hab
      have hb : ∀ i, ab.2 i ≤ 1 := by
        intro i
        have hEq := congrArg (fun f : I →₀ ℕ => f i) (Finset.mem_antidiagonal.mp hab)
        simp only [Finsupp.add_apply] at hEq
        have hi := he i
        omega
      rw [ih ab.2 hb, mul_zero]
  exact h p hp d hd

theorem quotient_coeff_eq (p q : MvPolynomial I ℂ)
    (h : Ideal.Quotient.mk (squareIdeal I) p = Ideal.Quotient.mk (squareIdeal I) q)
    (s : Finset I) : p.coeff (exponent s) = q.coeff (exponent s) := by
  have hp : p - q ∈ squareIdeal I := Ideal.Quotient.eq.mp h
  have hc := squareIdeal_coeff_zero (p - q) hp (exponent s) (exponent_le_one s)
  rw [coeff_sub] at hc
  exact sub_eq_zero.mp hc

omit [DecidableEq I] in
theorem quotient_monomial (s : Finset I) (c : ℂ) :
    Ideal.Quotient.mk (squareIdeal I) (MvPolynomial.monomial (exponent s) c) =
      scalar c * monomial s := by
  rw [exponent, MvPolynomial.monomial_sum_index]
  simp only [map_mul, map_prod, scalar, monomial, rowVariable]
  rfl

theorem scalar_monomial_injective (s : Finset I) (a b : ℂ)
    (h : scalar a * monomial s = scalar b * monomial s) : a = b := by
  have he : Ideal.Quotient.mk (squareIdeal I) (MvPolynomial.monomial (exponent s) a) =
      Ideal.Quotient.mk (squareIdeal I) (MvPolynomial.monomial (exponent s) b) := by
    rw [quotient_monomial, quotient_monomial]
    exact h
  have hc := quotient_coeff_eq _ _ he s
  simpa only [coeff_monomial, ite_true] using hc

end ResearchMain.Chollet.RankCoefficients
