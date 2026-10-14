import MainTheorems.Corona.Shape
import MainTheorems.Hypercomb.Coefficients

namespace ResearchMain.Corona

open Polynomial
open ResearchMain.Hypercomb

noncomputable def symmetricQuadratic (r : ℝ) : ℝ[X] := 1 + C r * X + X ^ 2

theorem symmetricQuadratic_power_positiveLC {r : ℝ} (hr : 1 ≤ r) (m : ℕ) :
    PositiveLC (coefficientSequence (symmetricQuadratic r ^ m)) (2 * m) := by
  induction m with
  | zero => simpa only [pow_zero, mul_zero] using coefficientSequence_one_positiveLC
  | succ m ih =>
    have h := ih.coefficients_quadratic (b := r) (c := 1) (by linarith) (by norm_num)
      (by nlinarith)
    simpa only [map_one, one_mul, symmetricQuadratic, pow_succ,
      show 2 * m + 2 = 2 * (m + 1) by omega] using h

theorem symmetricQuadratic_power_symmetric (r : ℝ) (m : ℕ) (k : ℤ) :
    coefficientSequence (symmetricQuadratic r ^ m) (2 * m - k) =
      coefficientSequence (symmetricQuadratic r ^ m) k := by
  induction m generalizing k with
  | zero => simp [coefficientSequence_one]
  | succ m ih =>
    have he (j : ℤ) : coefficientSequence (symmetricQuadratic r ^ (m + 1)) j =
        coefficientSequence (symmetricQuadratic r ^ m) j +
        r * coefficientSequence (symmetricQuadratic r ^ m) (j - 1) +
        coefficientSequence (symmetricQuadratic r ^ m) (j - 2) := by
      rw [pow_succ, symmetricQuadratic]
      simpa only [map_one, one_mul, tripleSum, symmetricQuadratic] using
        coefficientSequence_trinomial (symmetricQuadratic r ^ m) r 1 j
    rw [he, he]
    have h₀ := ih (k - 2)
    have h₁ := ih (k - 1)
    have h₂ := ih k
    simp only [Nat.cast_succ] at *
    ring_nf at h₀ h₁ h₂ ⊢
    rw [h₀, h₁, h₂]
    ring

theorem symmetricQuadratic_power_increasing {r : ℝ} (hr : 1 ≤ r) (m : ℕ)
    {k : ℤ} (hk : k < m) :
    coefficientSequence (symmetricQuadratic r ^ m) k ≤
      coefficientSequence (symmetricQuadratic r ^ m) (k + 1) := by
  have h := (symmetricQuadratic_power_positiveLC hr m).ratioDecreasing
    (2 * m - k - 1) (k + 1) (by omega)
  rw [show 2 * (m : ℤ) - k - 1 + 1 = 2 * m - k by ring,
    show k + 1 - 1 = k by ring, symmetricQuadratic_power_symmetric,
    show 2 * (m : ℤ) - k - 1 = 2 * m - (k + 1) by ring,
    symmetricQuadratic_power_symmetric] at h
  have h₀ := (symmetricQuadratic_power_positiveLC hr m).nonnegative k
  have h₁ := (symmetricQuadratic_power_positiveLC hr m).nonnegative (k + 1)
  nlinarith

theorem symmetricQuadratic_power_decreasing {r : ℝ} (hr : 1 ≤ r) (m : ℕ)
    {k : ℤ} (hk : (m : ℤ) ≤ k) :
    coefficientSequence (symmetricQuadratic r ^ m) (k + 1) ≤
      coefficientSequence (symmetricQuadratic r ^ m) k := by
  have h := symmetricQuadratic_power_increasing hr m
    (k := 2 * m - k - 1) (by omega)
  rw [show 2 * (m : ℤ) - k - 1 = 2 * m - (k + 1) by ring,
    symmetricQuadratic_power_symmetric,
    show 2 * (m : ℤ) - (k + 1) + 1 = 2 * m - k by ring,
    symmetricQuadratic_power_symmetric] at h
  exact h

theorem coefficientSequence_X_pow_mul (j : ℕ) (p : ℝ[X]) (k : ℤ) :
    coefficientSequence (X ^ j * p) k = coefficientSequence p (k - j) := by
  induction j generalizing k with
  | zero => simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
  | succ j ih =>
    have he : (X : ℝ[X]) ^ (j + 1) * p = (X ^ j * p) * X := by ring
    rw [he, coefficientSequence_mul_X, ih]
    congr 1
    simp only [Nat.cast_succ]
    ring

theorem symmetricQuadratic_shift_unimodal {r : ℝ} (hr : 1 ≤ r) {N j : ℕ} (hj : j ≤ N) :
    UnimodalAt (fun k => (X ^ j * symmetricQuadratic r ^ (N - j)).coeff k) N := by
  have he (k : ℕ) : (X ^ j * symmetricQuadratic r ^ (N - j)).coeff k =
      coefficientSequence (symmetricQuadratic r ^ (N - j)) ((k : ℤ) - j) := by
    have h := coefficientSequence_X_pow_mul j (symmetricQuadratic r ^ (N - j)) k
    simpa only [coefficientSequence, Nat.cast_nonneg, ite_true, Int.toNat_natCast] using h
  constructor
  · intro k hk
    dsimp only
    rw [he, he]
    have h := symmetricQuadratic_power_increasing hr (N - j) (k := (k : ℤ) - j) (by omega)
    simpa only [Nat.cast_succ, sub_add_eq_add_sub] using h
  · intro k hk
    dsimp only
    rw [he, he]
    have h := symmetricQuadratic_power_decreasing hr (N - j) (k := (k : ℤ) - j) (by omega)
    simpa only [Nat.cast_succ, sub_add_eq_add_sub] using h

end ResearchMain.Corona
