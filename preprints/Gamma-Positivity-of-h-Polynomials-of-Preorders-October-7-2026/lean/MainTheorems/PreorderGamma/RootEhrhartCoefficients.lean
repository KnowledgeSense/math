import MainTheorems.PreorderGamma.RootEhrhart
import MainTheorems.PreorderGamma.GammaProperties
import Mathlib.Algebra.Polynomial.Degree.Support

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

theorem polynomial_inverse_series_coeff (p : Polynomial ℚ) (n m t : ℕ)
    (hp : p.natDegree < m) :
    PowerSeries.coeff t ((p : PowerSeries ℚ) *
      (PowerSeries.invOneSubPow ℚ (n + 1)).val) =
        ∑ k ∈ Finset.range m, p.coeff k *
          if k ≤ t then (Nat.choose (n + (t - k)) n : ℚ) else 0 := by
  have hpoly : (p : PowerSeries ℚ) = ∑ k ∈ Finset.range m,
      PowerSeries.C (p.coeff k) * PowerSeries.X ^ k := by
    have h := congrArg Polynomial.coeToPowerSeries.ringHom
      (Polynomial.as_sum_range_C_mul_X_pow' p hp)
    simpa only [map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X] using h
  rw [hpoly, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp only [PowerSeries.coeff_mk]

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem root_lattice_count_ehrhart_formula (t : ℕ) :
    rootLatticeCount (E := E) t =
      ∑ k ∈ Finset.range (Fintype.card E + 1),
        (supportPolynomial (E := E)).coeff k *
          if k ≤ t then Nat.choose (2 * Fintype.card E + (t - k))
            (2 * Fintype.card E) else 0 := by
  apply Nat.cast_injective (R := ℚ)
  rw [← rootEhrhartSeries_coeff t, root_ehrhart_series,
    polynomial_inverse_series_coeff _ (2 * Fintype.card E) (Fintype.card E + 1) t (by
      apply lt_of_le_of_lt (Polynomial.natDegree_map_le
        (p := supportPolynomial (E := E)) (f := Nat.castRingHom ℚ))
      rw [supportPolynomial_natDegree]
      omega)]
  simp only [Polynomial.coeff_map, Nat.coe_castRingHom, Nat.cast_sum, Nat.cast_mul,
    Nat.cast_ite, Nat.cast_zero]

theorem root_lattice_count_binomial (t : ℕ) :
    rootLatticeCount (E := E) t =
      ∑ k ∈ Finset.range (Fintype.card E + 1),
        (supportPolynomial (E := E)).coeff k *
          Nat.choose (2 * Fintype.card E + t - k) (2 * Fintype.card E) := by
  rw [root_lattice_count_ehrhart_formula]
  apply Finset.sum_congr rfl
  intro k hk
  apply congrArg (fun v : ℕ => (supportPolynomial (E := E)).coeff k * v)
  by_cases hkt : k ≤ t
  · rw [ite_eq_left hkt]
    congr 1
    omega
  · rw [ite_eq_right hkt]
    have hkbound := Finset.mem_range.mp hk
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm

theorem root_lattice_count_zero : rootLatticeCount (E := E) 0 = 1 := by
  simp [root_lattice_count_ehrhart_formula, supportPolynomial_coeff_zero]

end ResearchMain.PreorderGamma
