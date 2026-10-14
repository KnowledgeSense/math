import SphericalTreeFailures.HardCoreDistribution
import SphericalTreeFailures.PathMean

namespace SphericalTreeFailures
set_option backward.isDefEq.respectTransparency false
open Finset Polynomial MeasureTheory
variable {V : Type*} [Fintype V]

instance (G : SimpleGraph V) : MeasurableSpace (IndependentConfiguration G) := ⊤
instance (G : SimpleGraph V) : MeasurableSingletonClass (IndependentConfiguration G) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

theorem eulerPolynomial_X_pow (n : ℕ) : eulerPolynomial (X ^ n) = C n * X ^ n := by
  ext j
  rw [eulerPolynomial_coeff, coeff_C_mul]
  by_cases h : n = j <;> simp [coeff_X_pow, h, eq_comm]

theorem euler_independencePolynomial_eval (G : SimpleGraph V) (activity : ℝ) :
    (eulerPolynomial (independencePolynomial G univ)).eval₂ (Nat.castRingHom ℝ) activity =
      ∑ s ∈ independentSetsWithin G univ, (s.card : ℝ) * activity ^ s.card := by
  classical
  have he : eulerPolynomial (independencePolynomial G univ) =
      ∑ s ∈ independentSetsWithin G univ, C s.card * X ^ s.card := by
    unfold independencePolynomial
    calc
      eulerPolynomial (∑ s ∈ independentSetsWithin G univ, X ^ s.card) =
          ∑ s ∈ independentSetsWithin G univ, eulerPolynomial (X ^ s.card) := by
        simp [eulerPolynomial, map_sum, mul_sum]
      _ = _ := by simp_rw [eulerPolynomial_X_pow]
  rw [he, eval₂_finsetSum]
  apply sum_congr rfl
  intro s hs
  simp only [eval₂_mul, eval₂_C, eval₂_X_pow]
  rfl

/-- The logarithmic derivative is the expected size of an actual hard-core independent set. -/
theorem hardCore_expected_size (G : SimpleGraph V) (activity : ℝ) (ha : 0 < activity) :
    (∫ s : IndependentConfiguration G, (s.val.card : ℝ) ∂(hardCore G activity ha).toMeasure) =
      polynomialMean (independencePolynomial G univ) activity := by
  classical
  have hz := configurationPartition_pos G ha
  rw [PMF.integral_eq_sum]
  simp only [hardCore_apply, smul_eq_mul]
  have hw (s : IndependentConfiguration G) :
      (ENNReal.ofReal (activity ^ s.val.card / configurationPartition G activity)).toReal =
        activity ^ s.val.card / configurationPartition G activity :=
    ENNReal.toReal_ofReal (by positivity)
  simp_rw [hw]
  unfold polynomialMean
  rw [euler_independencePolynomial_eval, ← configurationPartition_polynomial]
  trans ∑ s ∈ independentSetsWithin G univ, activity ^ s.card / configurationPartition G activity * (s.card : ℝ)
  · exact Finset.sum_coe_sort (independentSetsWithin G univ)
      (fun s : Finset V => activity ^ s.card / configurationPartition G activity * (s.card : ℝ))
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro s hs
  ring

theorem independentConfiguration_size_le (G : SimpleGraph V) (s : IndependentConfiguration G) :
    s.val.card ≤ Fintype.card V := Finset.card_le_univ _

theorem hardCore_mean_bounds (G : SimpleGraph V) (activity : ℝ) (ha : 0 < activity) :
    0 ≤ polynomialMean (independencePolynomial G univ) activity ∧
      polynomialMean (independencePolynomial G univ) activity ≤ Fintype.card V := by
  rw [← hardCore_expected_size G activity ha]
  constructor
  · exact integral_nonneg (fun s => Nat.cast_nonneg _)
  · have h := integral_mono (μ := (hardCore G activity ha).toMeasure)
      (f := fun s : IndependentConfiguration G => (s.val.card : ℝ))
      (g := fun _ => (Fintype.card V : ℝ)) Integrable.of_finite (integrable_const _)
      (fun s => by dsimp; exact_mod_cast independentConfiguration_size_le G s)
    simpa using h

end SphericalTreeFailures
