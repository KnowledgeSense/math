import Fan.SeriesCoefficientTransform
import Mathlib.RingTheory.PowerSeries.Derivative

/-! Finite coefficient change of variable for the inverse-Z generating series. -/
namespace Fan
open PowerSeries Finset
variable {R : Type*} [CommRing R]

/-- Multiplication after a zero-constant substitution still uses a finite coefficient sum. -/
theorem coeff_subst_X_mul_product (f u v : PowerSeries R) (n : ℕ) :
    coeff n (f.subst (X * u) * v) =
      ∑ k ∈ range (n + 1), coeff k f * coeff (n - k) (u ^ k * v) := by
  let p : PowerSeries R := ∑ k ∈ range (n + 1), C (coeff k f) * X ^ k
  have hp (i : ℕ) (hi : i ≤ n) : coeff i p = coeff i f := by
    dsimp [p]
    simp only [map_sum, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq]
    simp [hi]
  have hsub (i : ℕ) (hi : i ≤ n) :
      coeff i (f.subst (X * u)) = coeff i (p.subst (X * u)) := by
    rw [coeff_subst_X_mul, coeff_subst_X_mul]
    apply sum_congr rfl
    intro k hk
    rw [hp k (by have := mem_range.mp hk; omega)]
  have hprod : coeff n (f.subst (X * u) * v) = coeff n (p.subst (X * u) * v) := by
    rw [coeff_mul, coeff_mul]
    apply sum_congr rfl
    intro a ha
    rw [hsub a.1 (by have ha' := Finset.mem_antidiagonal.mp ha; omega)]
  rw [hprod]
  have hz : HasSubst ((X : PowerSeries R) * u) := HasSubst.of_constantCoeff_zero' (by simp)
  have he : p.subst (X * u) = ∑ k ∈ range (n + 1), C (coeff k f) * (X * u) ^ k := by
    rw [← PowerSeries.coe_substAlgHom hz]
    dsimp [p]
    simp only [map_sum, map_mul, map_pow, PowerSeries.substAlgHom_X,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_C]
    rfl
  rw [he, sum_mul, map_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using mem_range.mp hk
  rw [mul_pow]
  have ht : C (coeff k f) * (X ^ k * u ^ k) * v = C (coeff k f) * (X ^ k * (u ^ k * v)) := by ring
  rw [ht, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hkn]

end Fan

namespace Fan
open PowerSeries Finset
variable {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]

omit [NoZeroDivisors R] [CharZero R] in
private theorem inverse_power_cancel (u v : PowerSeries R) (h : u * v = 1)
    (a b : ℕ) (hab : a ≤ b) : u ^ a * v ^ b = v ^ (b - a) := by
  calc
    _ = (u * v) ^ a * v ^ (b - a) := by rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_of_le hab]
    _ = _ := by rw [h, one_pow, one_mul]

private theorem jacobian_diagonal (u v : PowerSeries R) (h : u * v = 1) (m : ℕ) :
    coeff m (v ^ (m + 1) * derivative (X * u)) = if m = 0 then 1 else 0 := by
  have hd := congrArg (derivative (R := R)) h
  rw [derivative_one, Derivation.leibniz] at hd
  have hvd : v ^ 2 * derivative u = -derivative v := by
    linear_combination v * hd - derivative v * h
  have hcancel : v * u = 1 := by rw [mul_comm, h]
  cases m with
  | zero =>
    simp only [zero_add, pow_one, ↓reduceIte]
    rw [Derivation.leibniz, derivative_X]
    simp only [smul_eq_mul]
    have he : v * (X * derivative u + u * 1) = 1 + X * (v * derivative u) := by
      linear_combination hcancel
    rw [he, map_add, coeff_zero_X_mul, add_zero]
    simp
  | succ m =>
    rw [ite_eq_right (Nat.succ_ne_zero m)]
    have he : v ^ (m + 1 + 1) * derivative (X * u) =
        v ^ (m + 1) - X * (v ^ m * derivative v) := by
      rw [Derivation.leibniz, derivative_X]
      linear_combination v ^ m * X * hvd + v ^ (m + 1) * hcancel
    change coeff (m + 1) _ = 0
    rw [he, map_sub, coeff_succ_X_mul]
    have hc' : coeff (m + 1) (v ^ (m + 1)) * (m + 1 : R) =
        (m + 1 : R) * coeff m (v ^ m * derivative v) := by
      have hh := congrArg (coeff m) (derivative_pow v (m + 1))
      rw [coeff_derivative, Nat.add_sub_cancel, mul_assoc, coeff_natCast_mul] at hh
      exact_mod_cast hh
    have hn : (m + 1 : R) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    apply (mul_eq_zero.mp (show (m + 1 : R) *
      (coeff (m + 1) (v ^ (m + 1)) - coeff m (v ^ m * derivative v)) = 0 by
        linear_combination hc')).resolve_left hn

/-- Formal coefficient change of variable, proved by finite substitution and the Jacobian. -/
theorem coeff_change_variable (f u v : PowerSeries R) (h : u * v = 1) (n : ℕ) :
    coeff n f = coeff n (f.subst (X * u) * (v ^ (n + 1) * derivative (X * u))) := by
  rw [coeff_subst_X_mul_product]
  have he (k : ℕ) (hk : k ≤ n) :
      coeff (n - k) (u ^ k * (v ^ (n + 1) * derivative (X * u))) =
        if k = n then 1 else 0 := by
    rw [← mul_assoc, inverse_power_cancel u v h k (n + 1) (by omega),
      show n + 1 - k = (n - k) + 1 by omega, jacobian_diagonal u v h]
    by_cases hkn : k = n
    · simp [hkn]
    · rw [ite_eq_right hkn, ite_eq_right (by omega)]
  calc
    _ = ∑ k ∈ range (n + 1), coeff k f * (if k = n then 1 else 0) := by simp
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      rw [he k (by simpa using mem_range.mp hk)]

end Fan
