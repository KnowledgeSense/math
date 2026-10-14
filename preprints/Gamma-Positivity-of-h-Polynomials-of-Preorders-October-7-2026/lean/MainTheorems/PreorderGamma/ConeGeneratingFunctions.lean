import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

theorem positive_cone_series_coeff (k t : ℕ) :
    PowerSeries.coeff t ((PowerSeries.X : PowerSeries ℚ) ^ k *
      (PowerSeries.invOneSubPow ℚ (k + 1)).val) = (Nat.choose t k : ℚ) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp only [PowerSeries.coeff_mk]
  by_cases h : k ≤ t
  · rw [ite_eq_left h, show k + (t - k) = t by omega]
  · rw [ite_eq_right h, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

theorem cone_series_numerator_term (n k : ℕ) (hk : k ≤ n) :
    ((PowerSeries.X : PowerSeries ℚ) ^ k *
      (PowerSeries.invOneSubPow ℚ (k + 1)).val) * (1 - PowerSeries.X) ^ (n + 1) =
        PowerSeries.X ^ k * (1 - PowerSeries.X) ^ (n - k) := by
  rw [mul_assoc]
  congr 1
  rw [mul_comm, show n + 1 = (n - k) + (k + 1) by omega]
  exact PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow ℚ (n - k) (k + 1)

noncomputable def coneFaceSeries {A : Type*} (F : Finset A) (k : A → ℕ) : PowerSeries ℚ :=
  ∑ a ∈ F, PowerSeries.X ^ k a * (PowerSeries.invOneSubPow ℚ (k a + 1)).val

noncomputable def coneFaceNumerator {A : Type*} (n : ℕ) (F : Finset A) (k : A → ℕ) :
    Polynomial ℚ :=
  ∑ a ∈ F, Polynomial.X ^ k a * (1 - Polynomial.X) ^ (n - k a)

theorem coneFaceSeries_coeff {A : Type*} (F : Finset A) (k : A → ℕ) (t : ℕ) :
    PowerSeries.coeff t (coneFaceSeries F k) =
      ∑ a ∈ F, (Nat.choose t (k a) : ℚ) := by
  rw [coneFaceSeries, map_sum]
  simp only [positive_cone_series_coeff]

theorem coneFaceSeries_numerator {A : Type*} (n : ℕ) (F : Finset A) (k : A → ℕ)
    (hk : ∀ a ∈ F, k a ≤ n) :
    coneFaceSeries F k * (1 - PowerSeries.X : PowerSeries ℚ) ^ (n + 1) =
      (coneFaceNumerator n F k : PowerSeries ℚ) := by
  rw [coneFaceSeries, Finset.sum_mul]
  calc
    _ = ∑ a ∈ F, (PowerSeries.X : PowerSeries ℚ) ^ k a *
        (1 - PowerSeries.X) ^ (n - k a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact cone_series_numerator_term n (k a) (hk a ha)
    _ = _ := by
      change _ = Polynomial.coeToPowerSeries.ringHom (coneFaceNumerator n F k)
      rw [coneFaceNumerator]
      simp only [map_sum, map_mul, map_pow, map_sub, map_one,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

end ResearchMain.PreorderGamma
