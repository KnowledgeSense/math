import GenericValueSemigroups.ExponentialColumns
import GenericValueSemigroups.FormalValues

namespace GenericValueSemigroups
open Finset

noncomputable def formalExponential {R : Type*} [CommRing R] [Algebra ℚ R] (s : R) :
    PowerSeries R := PowerSeries.rescale s (PowerSeries.exp R)

theorem formalExponential_add {R : Type*} [CommRing R] [Algebra ℚ R] (s t : R) :
    formalExponential (s+t) = formalExponential s * formalExponential t :=
  (PowerSeries.exp_mul_exp_eq_exp_add s t).symm

@[simp] theorem formalExponential_zero {R : Type*} [CommRing R] [Algebra ℚ R] :
    formalExponential (0 : R) = 1 := by
  simp [formalExponential, PowerSeries.rescale_zero]

theorem formalExponential_pow {R : Type*} [CommRing R] [Algebra ℚ R] (s : R) (n : ℕ) :
    formalExponential s ^ n = formalExponential ((n : R)*s) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← formalExponential_add]; congr 1; push_cast; ring

theorem formalExponential_sum {R ι : Type*} [CommRing R] [Algebra ℚ R]
    (S : Finset ι) (s : ι → R) :
    formalExponential (∑ i ∈ S, s i) = ∏ i ∈ S, formalExponential (s i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, formalExponential_add, ih]

noncomputable def exponentialCoordinate {R : Type*} [CommRing R] [Algebra ℚ R]
    (r : ℕ) (s : R) : PowerSeries R := PowerSeries.X^r * formalExponential s

theorem exponentialCoordinate_monomial {R : Type*} [CommRing R] [Algebra ℚ R]
    {d : ℕ} (r α : Fin d → ℕ) (node : Fin d → R) :
    (∏ i, exponentialCoordinate (r i) (node i) ^ α i) =
      exponentialCoordinate (∑ i, α i*r i) (∑ i, (α i : R)*node i) := by
  simp only [exponentialCoordinate, mul_pow, ← pow_mul, formalExponential_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← formalExponential_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

@[simp] theorem coeff_formalExponential_real (s : ℝ) (n : ℕ) :
    PowerSeries.coeff n (formalExponential s) = s^n / (Nat.factorial n : ℝ) := by
  simp [formalExponential, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, div_eq_mul_inv,
    mul_comm]

theorem coeff_exponentialCoordinate_real (r : ℕ) (s : ℝ) (n : ℕ) :
    PowerSeries.coeff n (exponentialCoordinate r s) =
      if r ≤ n then s^(n-r)/(Nat.factorial (n-r) : ℝ) else 0 := by
  simp [exponentialCoordinate, PowerSeries.coeff_X_pow_mul']

theorem coeff_exponentialCoordinate_below {R : Type*} [CommRing R] [Algebra ℚ R]
    (r : ℕ) (s : R) (n : ℕ) (hn : n < r) :
    PowerSeries.coeff n (exponentialCoordinate r s) = 0 := by
  simp [exponentialCoordinate, PowerSeries.coeff_X_pow_mul', Nat.not_le.mpr hn]

@[simp] theorem coeff_exponentialCoordinate_leading {R : Type*} [CommRing R] [Algebra ℚ R]
    (r : ℕ) (s : R) : PowerSeries.coeff r (exponentialCoordinate r s) = 1 := by
  simp [exponentialCoordinate, PowerSeries.coeff_X_pow_mul', formalExponential,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp]

theorem order_exponentialCoordinate {R : Type*} [CommRing R] [Algebra ℚ R] [Nontrivial R]
    (r : ℕ) (s : R) : PowerSeries.order (exponentialCoordinate r s) = r := by
  apply PowerSeries.order_eq_nat.mpr
  exact ⟨by simp, fun n hn => coeff_exponentialCoordinate_below r s n hn⟩

end GenericValueSemigroups
