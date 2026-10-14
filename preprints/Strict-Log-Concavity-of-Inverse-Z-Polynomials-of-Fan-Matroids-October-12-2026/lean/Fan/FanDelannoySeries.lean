import Fan.FanLagrangeSubstitution
import Fan.KernelConvolutionRecurrence

noncomputable section
open scoped BigOperators
namespace Fan
open Finset

def fanDelannoyRow (j : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range (j + 1), Polynomial.monomial k ((2 : ℝ)^j * delannoy (1/2) k (j-k))

@[simp] theorem fanDelannoyRow_coeff (j k : ℕ) :
    (fanDelannoyRow j).coeff k =
      if k ≤ j then (2 : ℝ)^j * delannoy (1/2) k (j-k) else 0 := by
  simp [fanDelannoyRow, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

@[simp] theorem fanDelannoyRow_zero : fanDelannoyRow 0 = 1 := by
  ext k
  cases k <;> simp [Polynomial.coeff_one]

@[simp] theorem fanDelannoyRow_one : fanDelannoyRow 1 = 2 * (1 + Polynomial.X) := by
  ext k
  cases k with
  | zero => simp
  | succ k => cases k <;> simp [Polynomial.coeff_one, Polynomial.coeff_X]

theorem fanDelannoyRow_recurrence (j : ℕ) :
    fanDelannoyRow (j+2) = 2 * (1 + Polynomial.X) * fanDelannoyRow (j+1) -
      2 * Polynomial.X * fanDelannoyRow j := by
  ext k
  rw [show (2 : Polynomial ℝ) * (1 + Polynomial.X) * fanDelannoyRow (j+1) -
      2 * Polynomial.X * fanDelannoyRow j =
    2 * fanDelannoyRow (j+1) + Polynomial.X * (2 * fanDelannoyRow (j+1)) -
      Polynomial.X * (2 * fanDelannoyRow j) by ring]
  cases k with
  | zero => simp [pow_succ]; ring
  | succ k =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_mul,
      Polynomial.coeff_ofNat_mul, fanDelannoyRow_coeff]
    by_cases hk : k ≤ j
    · simp only [show k+1 ≤ j+2 by omega, show k+1 ≤ j+1 by omega,
        show k ≤ j+1 by omega, hk, ite_true]
      have h := delannoy_cross (1/2) k (j-k)
      rw [show j-k+1 = j+1-k by omega] at h
      rw [show j+2-(k+1) = j+1-k by omega,
        show j+1-(k+1) = j-k by omega]
      simp only [pow_succ] at *
      linear_combination (2 : ℝ)^(j+2) * h
    · by_cases he : k = j+1
      · subst k
        simp [pow_succ]
        ring
      · simp [show ¬k+1 ≤ j+2 by omega, show ¬k+1 ≤ j+1 by omega,
          show ¬k ≤ j+1 by omega, hk]

def fanDelannoySeries : PowerSeries (Polynomial ℝ) := PowerSeries.mk fanDelannoyRow

@[simp] theorem fanDelannoySeries_coeff (j : ℕ) :
    PowerSeries.coeff j fanDelannoySeries = fanDelannoyRow j := by
  simp [fanDelannoySeries]

@[simp] theorem fanDelannoySeries_constantCoeff :
    fanDelannoySeries.constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, fanDelannoySeries_coeff, fanDelannoyRow_zero]

theorem fanDelannoySeries_inverse :
    fanDelannoySeries *
      (1 - 2 * PowerSeries.C (1 + Polynomial.X) * PowerSeries.X +
        2 * PowerSeries.C Polynomial.X * PowerSeries.X ^ 2) = 1 := by
  ext j : 1
  rw [show fanDelannoySeries *
      (1 - 2 * PowerSeries.C (1 + Polynomial.X) * PowerSeries.X +
        2 * PowerSeries.C Polynomial.X * PowerSeries.X ^ 2) =
      fanDelannoySeries - PowerSeries.X *
        (PowerSeries.C (2 * (1 + Polynomial.X)) * fanDelannoySeries) +
      PowerSeries.X ^ 2 * (PowerSeries.C (2 * Polynomial.X) * fanDelannoySeries) by
        simp only [map_mul, map_ofNat]; ring]
  cases j with
  | zero => simp
  | succ j => cases j with
    | zero => simp [PowerSeries.coeff_X_pow_mul']
    | succ j =>
      simp only [map_add, map_sub, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_X_pow_mul', show 2 ≤ j+1+1 by omega, ite_true,
        show j+1+1-2 = j by omega, PowerSeries.coeff_C_mul, fanDelannoySeries_coeff,
        PowerSeries.coeff_one, show j+1+1 ≠ 0 by omega, ite_false]
      rw [show j+1+1 = j+2 by omega, fanDelannoyRow_recurrence]
      ring

def fanRationalH (t : Polynomial ℝ) : PowerSeries (Polynomial ℝ) :=
  (geometricSeries (1 : Polynomial ℝ)).subst
    (2 * PowerSeries.C (1+t) * PowerSeries.X - 2 * PowerSeries.C t * PowerSeries.X ^ 2)

theorem fanRationalH_eq : fanRationalH Polynomial.X = fanDelannoySeries := by
  let d : PowerSeries (Polynomial ℝ) :=
    1 - 2 * PowerSeries.C (1 + Polynomial.X) * PowerSeries.X +
        2 * PowerSeries.C Polynomial.X * PowerSeries.X ^ 2
  have h1 : fanRationalH Polynomial.X * d = 1 := by
    have h := geometricSeries_subst_inverse (1 : Polynomial ℝ)
      (2 * PowerSeries.C (1 + Polynomial.X) * PowerSeries.X -
        2 * PowerSeries.C Polynomial.X * PowerSeries.X ^ 2) (by simp)
    simp only [map_one, one_mul] at h
    dsimp [fanRationalH, d]
    linear_combination h
  have h2 : fanDelannoySeries * d = 1 := fanDelannoySeries_inverse
  calc
    fanRationalH Polynomial.X = fanRationalH Polynomial.X * (fanDelannoySeries * d) := by rw [h2, mul_one]
    _ = fanDelannoySeries * (fanRationalH Polynomial.X * d) := by ring
    _ = fanDelannoySeries := by rw [h1, mul_one]

theorem two_mul_fanRationalY (t : Polynomial ℝ) :
    2 * fanRationalY t = 1 + fanRationalH t := by
  have h := geometricSeries_subst_inverse (1 : Polynomial ℝ)
    (2 * PowerSeries.C (1+t) * PowerSeries.X -
      2 * PowerSeries.C t * PowerSeries.X ^ 2) (by simp)
  simp only [map_one, one_mul] at h
  dsimp [fanRationalY, fanRationalH]
  linear_combination h

theorem fanRationalY_coeff (j : ℕ) (hj : 0 < j) :
    2 * PowerSeries.coeff j (fanRationalY Polynomial.X) = fanDelannoyRow j := by
  have h := congrArg (PowerSeries.coeff j) (two_mul_fanRationalY Polynomial.X)
  rw [map_add, fanRationalH_eq, fanDelannoySeries_coeff, PowerSeries.coeff_one,
    ite_eq_right (by omega)] at h
  simpa only [PowerSeries.coeff_ofNat_mul, zero_add] using h

end Fan
