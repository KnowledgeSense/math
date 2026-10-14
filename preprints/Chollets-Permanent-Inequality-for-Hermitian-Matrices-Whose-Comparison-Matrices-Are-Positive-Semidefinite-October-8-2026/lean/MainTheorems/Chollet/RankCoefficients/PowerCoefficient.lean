import MainTheorems.Chollet.RankCoefficients.Coefficient
import Mathlib.Algebra.MvPolynomial.Coeff

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [DecidableEq I]

theorem exponent_support (s : Finset I) : (exponent s).support = s := by
  ext i
  simp only [Finsupp.mem_support_iff, exponent_apply]
  split_ifs <;> simp_all

theorem exponent_sum (s : Finset I) : (exponent s).sum (fun _ n => n) = s.card := by
  unfold Finsupp.sum
  rw [exponent_support]
  calc
    (∑ i ∈ s, exponent s i) = ∑ i ∈ s, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [exponent_apply, ite_eq_left hi]
    _ = s.card := by simp

theorem exponent_multinomial (s : Finset I) : (exponent s).multinomial = s.card.factorial := by
  rw [Finsupp.multinomial_eq, exponent_support]
  unfold Nat.multinomial
  have hs : (∑ i ∈ s, exponent s i) = s.card := by
    simpa only [Finsupp.sum, exponent_support] using exponent_sum s
  have hp : (∏ i ∈ s, (exponent s i).factorial) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [exponent_apply, ite_eq_left hi]
    rfl
  rw [hs, hp, Nat.div_one]

theorem exponent_prod (s : Finset I) (a : I → ℂ) :
    (exponent s).prod (fun i n => a i ^ n) = ∏ i ∈ s, a i := by
  unfold Finsupp.prod
  rw [exponent_support]
  apply Finset.prod_congr rfl
  intro i hi
  rw [exponent_apply, ite_eq_left hi]
  dsimp only
  rw [pow_one]

theorem linearPower_coeff [Fintype I] (a : I → ℂ) (s : Finset I) (k : ℕ) :
    ((∑ i, MvPolynomial.C (a i) * MvPolynomial.X i : MvPolynomial I ℂ) ^ k).coeff
      (exponent s) =
      if s.card = k then (k.factorial : ℂ) * ∏ i ∈ s, a i else 0 := by
  have he : (∑ i, MvPolynomial.C (a i) * MvPolynomial.X i : MvPolynomial I ℂ) =
      ∑ i, a i • MvPolynomial.X i := by
    simp only [MvPolynomial.smul_eq_C_mul]
  rw [he, MvPolynomial.coeff_linearCombination_X_pow_of_fintype,
    exponent_sum, exponent_multinomial, exponent_prod]
  split_ifs with hs
  · rw [hs]
  · rfl

end ResearchMain.Chollet.RankCoefficients
