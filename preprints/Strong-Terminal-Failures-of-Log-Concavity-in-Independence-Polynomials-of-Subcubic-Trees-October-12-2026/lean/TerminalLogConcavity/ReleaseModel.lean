import TerminalLogConcavity.GaussianModel
import TerminalLogConcavity.TerminalTransfer
import TerminalLogConcavity.SiteParameters
import TerminalLogConcavity.GaussianUpper

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

noncomputable def releaseModelPolynomial (q H : ℕ) : ℕ[X] :=
  C (selectedAmplifier q H ^ (2 * baseCoupling q * q * (q - 1))) *
    gaussianPolynomial q (selectedAmplifier q H) (selectedAmplifier q H ^ (2 * massParameter q))

theorem releaseModelPolynomial_lower {q H j : ℕ} (hj : j ≤ q) :
    releaseModel q H j ≤ ((releaseModelPolynomial q H).coeff j : ℝ) := by
  let a := selectedAmplifier q H
  let K := 2 * baseCoupling q * q * (q - 1)
  have hgauss : q.choose j * (a ^ (2 * massParameter q)) ^ j * a ^ (squareSum q + j ^ 2) ≤
      (gaussianPolynomial q a (a ^ (2 * massParameter q))).coeff j := by
    by_cases hz : j = 0
    · subst j; simpa using gaussian_constant_lower q a (a ^ (2 * massParameter q))
    · exact gaussian_coefficient_lower (by omega) hj
  have hmul := Nat.mul_le_mul_left (a ^ K) hgauss
  have hvalue : a ^ K * (q.choose j * (a ^ (2 * massParameter q)) ^ j * a ^ (squareSum q + j ^ 2)) =
      q.choose j * a ^ ((K + squareSum q) + (2 * massParameter q) * j + j ^ 2) := by
    rw [← pow_mul]
    calc
      _ = q.choose j * (a ^ K * a ^ (2 * massParameter q * j) * a ^ (squareSum q + j ^ 2)) := by ring
      _ = _ := by rw [← pow_add, ← pow_add]; congr 2; omega
  rw [hvalue] at hmul
  have hreal : (q.choose j : ℝ) * (a : ℝ) ^ ((K + squareSum q) + (2 * massParameter q) * j + j ^ 2) ≤
      (a : ℝ) ^ K * ((gaussianPolynomial q a (a ^ (2 * massParameter q))).coeff j : ℝ) := by
    exact_mod_cast hmul
  simpa only [releaseModel, modelCoefficient, releaseModelPolynomial, coeff_C_mul,
    Nat.cast_mul, Nat.cast_pow, a, K, baseCoupling, massParameter] using hreal

theorem releaseModelPolynomial_upper {q H j : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H) (hj : j ≤ q) :
    ((releaseModelPolynomial q H).coeff j : ℝ) ≤ 3 * releaseModel q H j := by
  have ha := selectedAmplifier_ge_128 (q := q) (H := H) (by omega) hH
  have hq4 := Nat.pow_le_pow_left hq 4
  have ha256 : 256 ≤ selectedAmplifier q H := by nlinarith
  let a := selectedAmplifier q H
  let K := 2 * baseCoupling q * q * (q - 1)
  have hg := gaussian_coefficient_upper (lam := a ^ (2 * massParameter q)) hq ha256 hj
  have hm := mul_le_mul_of_nonneg_left hg (show 0 ≤ (a : ℝ) ^ K by positivity)
  have he : (a : ℝ) ^ K *
      (3 * (q.choose j : ℝ) * ((a ^ (2 * massParameter q) : ℕ) : ℝ) ^ j *
        (a : ℝ) ^ (squareSum q + j ^ 2)) = 3 * releaseModel q H j := by
    simp only [Nat.cast_pow, releaseModel, modelCoefficient]
    change (a : ℝ) ^ K * (3 * (q.choose j : ℝ) * ((a : ℝ) ^ (2 * massParameter q)) ^ j *
      (a : ℝ) ^ (squareSum q + j ^ 2)) =
      3 * ((q.choose j : ℝ) * (a : ℝ) ^ (K + squareSum q + (2 * massParameter q) * j + j ^ 2))
    rw [← pow_mul]
    simp only [pow_add]
    ring
  rw [he] at hm
  simpa only [releaseModelPolynomial, coeff_C_mul, Nat.cast_mul, Nat.cast_pow, a, K] using hm

end TerminalLogConcavity
