import MainTheorems.Corona.Basic

namespace ResearchMain.Corona

open Classical Polynomial

noncomputable def eulerDerivative (p : ℝ[X]) : ℝ[X] := p.derivative * X
noncomputable def mass (p : ℝ[X]) : ℝ := p.eval 1
noncomputable def firstMoment (p : ℝ[X]) : ℝ := (eulerDerivative p).eval 1
noncomputable def secondMoment (p : ℝ[X]) : ℝ := (eulerDerivative (eulerDerivative p)).eval 1
noncomputable def mean (p : ℝ[X]) : ℝ := firstMoment p / mass p
noncomputable def variance (p : ℝ[X]) : ℝ := secondMoment p / mass p - mean p ^ 2
noncomputable def centeredSum (p : ℝ[X]) (t : ℝ) : ℝ :=
  ∑ k ∈ p.support, ((k : ℝ) - t) ^ 2 * p.coeff k

theorem eulerDerivative_coeff (p : ℝ[X]) (k : ℕ) :
    (eulerDerivative p).coeff k = (k : ℝ) * p.coeff k := by
  cases k with
  | zero => simp [eulerDerivative]
  | succ k =>
    rw [eulerDerivative, coeff_mul_X, coeff_derivative]
    push_cast
    ring

theorem eulerDerivative_support_subset (p : ℝ[X]) : (eulerDerivative p).support ⊆ p.support := by
  intro k hk
  rw [mem_support_iff, eulerDerivative_coeff] at hk
  rw [mem_support_iff]
  exact fun h => hk (by rw [h, mul_zero])

theorem mass_eq_sum (p : ℝ[X]) : mass p = ∑ k ∈ p.support, p.coeff k := by
  simp only [mass, eval_eq_sum, sum_def, one_pow, mul_one]

theorem firstMoment_eq_sum (p : ℝ[X]) :
    firstMoment p = ∑ k ∈ p.support, (k : ℝ) * p.coeff k := by
  rw [firstMoment, eval_eq_sum]
  rw [sum_eq_of_subset (fun n (a : ℝ) => a * (1 : ℝ) ^ n) (by simp)
    (eulerDerivative_support_subset p)]
  simp only [one_pow, mul_one, eulerDerivative_coeff]

theorem secondMoment_eq_sum (p : ℝ[X]) :
    secondMoment p = ∑ k ∈ p.support, (k : ℝ) ^ 2 * p.coeff k := by
  rw [secondMoment, eval_eq_sum]
  rw [sum_eq_of_subset (fun n (a : ℝ) => a * (1 : ℝ) ^ n) (by simp)
    ((eulerDerivative_support_subset (eulerDerivative p)).trans (eulerDerivative_support_subset p))]
  simp only [one_pow, mul_one, eulerDerivative_coeff]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem centeredSum_identity (p : ℝ[X]) (t : ℝ) :
    centeredSum p t = secondMoment p - 2 * t * firstMoment p + t ^ 2 * mass p := by
  rw [centeredSum, secondMoment_eq_sum, firstMoment_eq_sum, mass_eq_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem centeredSum_mean (p : ℝ[X]) (hp : mass p ≠ 0) :
    centeredSum p (mean p) = mass p * variance p := by
  rw [centeredSum_identity, variance, mean]
  field_simp
  ring

theorem eulerDerivative_mul (p q : ℝ[X]) :
    eulerDerivative (p * q) = eulerDerivative p * q + p * eulerDerivative q := by
  simp only [eulerDerivative, derivative_mul]
  ring

theorem eulerDerivative_add (p q : ℝ[X]) :
    eulerDerivative (p + q) = eulerDerivative p + eulerDerivative q := by
  simp only [eulerDerivative, derivative_add, add_mul]

theorem mass_mul (p q : ℝ[X]) : mass (p * q) = mass p * mass q := eval_mul

theorem firstMoment_mul (p q : ℝ[X]) :
    firstMoment (p * q) = firstMoment p * mass q + mass p * firstMoment q := by
  simp only [firstMoment, mass, eulerDerivative_mul, eval_add, eval_mul]

theorem secondMoment_mul (p q : ℝ[X]) :
    secondMoment (p * q) = secondMoment p * mass q + 2 * firstMoment p * firstMoment q +
      mass p * secondMoment q := by
  simp only [secondMoment, mass, firstMoment, eulerDerivative_mul, eulerDerivative_add, eval_add, eval_mul]
  ring

theorem mean_mul (p q : ℝ[X]) (hp : mass p ≠ 0) (hq : mass q ≠ 0) :
    mean (p * q) = mean p + mean q := by
  rw [mean, firstMoment_mul, mass_mul, mean, mean]
  field_simp

theorem variance_mul (p q : ℝ[X]) (hp : mass p ≠ 0) (hq : mass q ≠ 0) :
    variance (p * q) = variance p + variance q := by
  simp only [variance, mean, secondMoment_mul, firstMoment_mul, mass_mul]
  field_simp
  ring

theorem mass_pow (p : ℝ[X]) (n : ℕ) : mass (p ^ n) = mass p ^ n := eval_pow n

theorem mean_one : mean (1 : ℝ[X]) = 0 := by simp [mean, firstMoment, eulerDerivative]
theorem variance_one : variance (1 : ℝ[X]) = 0 := by
  simp [variance, mean, firstMoment, secondMoment, eulerDerivative]

theorem mean_pow (p : ℝ[X]) (hp : mass p ≠ 0) (n : ℕ) : mean (p ^ n) = n * mean p := by
  induction n with
  | zero => simp [mean_one]
  | succ n ih =>
    rw [pow_succ, mean_mul _ _ (by rw [mass_pow]; exact pow_ne_zero _ hp) hp, ih]
    push_cast
    ring

theorem variance_pow (p : ℝ[X]) (hp : mass p ≠ 0) (n : ℕ) :
    variance (p ^ n) = n * variance p := by
  induction n with
  | zero => simp [variance_one]
  | succ n ih =>
    rw [pow_succ, variance_mul _ _ (by rw [mass_pow]; exact pow_ne_zero _ hp) hp, ih]
    push_cast
    ring

end ResearchMain.Corona
