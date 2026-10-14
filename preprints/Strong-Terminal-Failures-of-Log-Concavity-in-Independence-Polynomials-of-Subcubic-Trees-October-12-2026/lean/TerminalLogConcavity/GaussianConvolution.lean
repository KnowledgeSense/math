import TerminalLogConcavity.RealCoefficientOrder
import TerminalLogConcavity.GaussianArithmetic
import TerminalLogConcavity.BinomialPolynomial
import Mathlib.RingTheory.PowerSeries.Basic

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

theorem polynomial_coeff_power {R : Type*} [CommSemiring R] (p : R[X]) (k j : ℕ) :
    (p ^ k).coeff j = ∑ l ∈ Finset.finsuppAntidiag (Finset.range k) j,
      ∏ i ∈ Finset.range k, p.coeff (l i) := by
  rw [← Polynomial.coeff_coe, Polynomial.coe_pow, PowerSeries.coeff_pow]
  simp only [Polynomial.coeff_coe]

theorem binomial_convolution (q k j : ℕ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.range k) j,
      ∏ i ∈ Finset.range k, q.choose (l i)) = (k * q).choose j := by
  have h := polynomial_coeff_power ((1 + X : ℕ[X]) ^ q) k j
  simp only [coeff_one_add_X_pow] at h
  rw [← pow_mul, coeff_one_add_X_pow] at h
  simpa [mul_comm] using h.symm

theorem gaussian_power_coefficient_bound {S : ℝ[X]} {q : ℕ} {a lam θ : ℝ}
    (hS : CoeffNonnegative S) (hzero : S.coeff 0 = 0)
    (ha : 1 ≤ a) (hlam : 0 ≤ lam) (hθ : 0 ≤ θ)
    (hcoeff : ∀ u, 1 ≤ u → S.coeff u ≤ θ * (q.choose u : ℝ) * lam ^ u * a ^ (u ^ 2))
    (k j : ℕ) :
    (S ^ k).coeff j ≤ θ ^ k * lam ^ j * a ^ (j ^ 2 - (k - 1) * j) * ((k * q).choose j : ℝ) := by
  rw [polynomial_coeff_power]
  have hv : (∑ l ∈ Finset.finsuppAntidiag (Finset.range k) j,
      ∏ i ∈ Finset.range k, (q.choose (l i) : ℝ)) = ((k * q).choose j : ℝ) := by
    exact_mod_cast binomial_convolution q k j
  rw [← hv, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hsum : ∑ i ∈ Finset.range k, l i = j := (Finset.mem_finsuppAntidiag.mp hl).1
  by_cases hpos : ∀ i ∈ Finset.range k, 1 ≤ l i
  · have hlist : ∀ u ∈ (List.range k).map l, 1 ≤ u := by
      intro u hu
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
      exact hpos i (by simpa using hi)
    have hgap := positive_composition_square_gap hlist
    have hrange : (List.range k).toFinset = Finset.range k := by
      ext i
      simp
    have hsquares : (∑ i ∈ Finset.range k, (l i) ^ 2) ≤ j ^ 2 - (k - 1) * j := by
      simp only [sumSquares, List.map_map, Function.comp_def, List.length_map,
        List.length_range] at hgap
      have hsumlist : ((List.range k).map l).sum = j := by
        rw [← List.sum_toFinset _ (show (List.range k).Nodup from List.nodup_range)]
        rw [hrange]
        exact hsum
      have hsquarelist : (((List.range k).map fun i => (l i) ^ 2)).sum =
          ∑ i ∈ Finset.range k, (l i) ^ 2 := by
        rw [← List.sum_toFinset _ (show (List.range k).Nodup from List.nodup_range)]
        rw [hrange]
      rw [hsumlist, hsquarelist] at hgap
      omega
    have hprod : (∏ i ∈ Finset.range k, S.coeff (l i)) ≤
        ∏ i ∈ Finset.range k, θ * (q.choose (l i) : ℝ) * lam ^ (l i) * a ^ ((l i) ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact hS _
      · intro i hi; exact hcoeff _ (hpos i hi)
    have hproduct : (∏ i ∈ Finset.range k, θ * (q.choose (l i) : ℝ) * lam ^ (l i) * a ^ ((l i) ^ 2)) =
        θ ^ k * lam ^ j * a ^ (∑ i ∈ Finset.range k, (l i) ^ 2) *
          (∏ i ∈ Finset.range k, (q.choose (l i) : ℝ)) := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Finset.prod_pow_eq_pow_sum, hsum]
      ring
    rw [hproduct] at hprod
    have hpow := pow_le_pow_right₀ ha hsquares
    have hm := mul_le_mul_of_nonneg_left hpow
      (by positivity : 0 ≤ θ ^ k * lam ^ j * (∏ i ∈ Finset.range k, (q.choose (l i) : ℝ)))
    exact hprod.trans (by convert hm using 1 <;> ring)
  · push Not at hpos
    obtain ⟨i, hi, hli⟩ := hpos
    have hz : l i = 0 := by omega
    have hprod : (∏ i ∈ Finset.range k, S.coeff (l i)) = 0 :=
      Finset.prod_eq_zero hi (by rw [hz, hzero])
    rw [hprod]
    positivity

theorem polynomial_power_coeff_zero_of_lt {R : Type*} [CommSemiring R] (S : R[X])
    (hzero : S.coeff 0 = 0) {j k : ℕ} (hjk : j < k) : (S ^ k).coeff j = 0 := by
  rw [polynomial_coeff_power]
  apply Finset.sum_eq_zero
  intro l hl
  have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
  have hex : ∃ i ∈ Finset.range k, l i = 0 := by
    by_contra hn
    push Not at hn
    have h := Finset.sum_le_sum (s := Finset.range k)
      (f := fun _ => 1) (g := fun i => l i) (fun i hi => by have := hn i hi; omega)
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h
    change (∑ i ∈ Finset.range k, l i) = j at hsum
    rw [hsum] at h
    omega
  obtain ⟨i, hi, hz⟩ := hex
  exact Finset.prod_eq_zero hi (by rw [hz, hzero])

end TerminalLogConcavity
