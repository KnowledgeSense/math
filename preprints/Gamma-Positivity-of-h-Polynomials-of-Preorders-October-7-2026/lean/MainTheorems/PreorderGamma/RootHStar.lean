import MainTheorems.PreorderGamma.RootEhrhartCoefficients
import MainTheorems.PreorderGamma.PreorderDuality
import Mathlib.RingTheory.PowerSeries.Trunc

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

noncomputable def rootHStarSeries : PowerSeries ℚ :=
  rootEhrhartSeries (E := E) *
    (1 - PowerSeries.X) ^ (2 * Fintype.card E + 1)

noncomputable def rootHStar : Polynomial ℚ :=
  PowerSeries.trunc (2 * Fintype.card E + 1) (rootHStarSeries (E := E))

theorem root_hStarSeries_support :
    rootHStarSeries (E := E) =
      ((supportPolynomial (E := E)).map (Nat.castRingHom ℚ) : PowerSeries ℚ) :=
  root_ehrhart_numerator

theorem root_hStar_support :
    rootHStar (E := E) = (supportPolynomial (E := E)).map (Nat.castRingHom ℚ) := by
  rw [rootHStar, root_hStarSeries_support]
  apply PowerSeries.trunc_coe_eq_self
  apply lt_of_le_of_lt (Polynomial.natDegree_map_le
    (p := supportPolynomial (E := E)) (f := Nat.castRingHom ℚ))
  rw [supportPolynomial_natDegree]
  omega

theorem root_hStar_coeff (k : ℕ) :
    (rootHStar (E := E)).coeff k = ((supportPolynomial (E := E)).coeff k : ℚ) := by
  rw [root_hStar_support, Polynomial.coeff_map]
  rfl

theorem root_hStar_natDegree :
    (rootHStar (E := E)).natDegree = Fintype.card E := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [root_hStar_support]
    exact (Polynomial.natDegree_map_le
      (p := supportPolynomial (E := E)) (f := Nat.castRingHom ℚ)).trans_eq
        supportPolynomial_natDegree
  · rw [root_hStar_coeff, supportPolynomial_coeff_top]
    norm_num

theorem root_hStar_monic : (rootHStar (E := E)).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one (Fintype.card E)
  · rw [root_hStar_natDegree]
  · rw [root_hStar_coeff, supportPolynomial_coeff_top]
    norm_num

theorem root_hStar_gamma_expansion :
    rootHStar (E := E) =
      ∑ k ∈ Finset.range (Fintype.card E / 2 + 1),
        Polynomial.C (gammaCoefficient (E := E) k : ℚ) * Polynomial.X ^ k *
          (1 + Polynomial.X) ^ (Fintype.card E - 2 * k) := by
  rw [root_hStar_support, preorder_gamma_expansion]
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_add, Polynomial.map_one,
    Nat.coe_castRingHom]

theorem root_hStar_coeff_nonnegative (k : ℕ) : 0 ≤ (rootHStar (E := E)).coeff k := by
  rw [root_hStar_coeff]
  exact Nat.cast_nonneg _

theorem root_hStar_coeff_symmetric (k : ℕ) (hk : k ≤ Fintype.card E) :
    (rootHStar (E := E)).coeff k = (rootHStar (E := E)).coeff (Fintype.card E - k) := by
  simp only [root_hStar_coeff, supportPolynomial_coeff_symmetric k hk]

theorem root_hStar_coeff_increasing (k : ℕ) (hk : k < Fintype.card E / 2) :
    (rootHStar (E := E)).coeff k ≤ (rootHStar (E := E)).coeff (k + 1) := by
  simp only [root_hStar_coeff]
  exact_mod_cast supportPolynomial_coeff_increasing k hk

theorem root_hStar_coeff_decreasing (k : ℕ)
    (hlo : Fintype.card E / 2 ≤ k) (hhi : k < Fintype.card E) :
    (rootHStar (E := E)).coeff (k + 1) ≤ (rootHStar (E := E)).coeff k := by
  simp only [root_hStar_coeff]
  exact_mod_cast supportPolynomial_coeff_decreasing k hlo hhi

theorem root_hStar_normalized :
    (rootHStar (E := E)).coeff 0 = 1 ∧
      (rootHStar (E := E)).coeff (Fintype.card E) = 1 := by
  simp [root_hStar_coeff, supportPolynomial_coeff_zero, supportPolynomial_coeff_top]

theorem root_hStar_orderDual :
    rootHStar (E := E) = rootHStar (E := OrderDual E) := by
  simpa only [root_hStar_support] using
    congrArg (fun p : Polynomial ℕ => p.map (Nat.castRingHom ℚ))
      (supportPolynomial_orderDual (E := E))

noncomputable def rootGVector (i : ℕ) : ℚ :=
  if i = 0 then (rootHStar (E := E)).coeff 0
  else (rootHStar (E := E)).coeff i - (rootHStar (E := E)).coeff (i - 1)

@[simp] theorem rootGVector_zero : rootGVector (E := E) 0 = 1 := by
  simp [rootGVector, root_hStar_coeff, supportPolynomial_coeff_zero]

@[simp] theorem rootGVector_succ (i : ℕ) :
    rootGVector (E := E) (i + 1) =
      (rootHStar (E := E)).coeff (i + 1) - (rootHStar (E := E)).coeff i := by
  simp [rootGVector]

theorem rootGVector_eq_support (i : ℕ) (hi : i ≤ Fintype.card E / 2) :
    rootGVector (E := E) i = (supportGVector (E := E) i : ℚ) := by
  cases i with
  | zero => simp
  | succ i =>
    simp only [rootGVector_succ, supportGVector_succ, root_hStar_coeff]
    exact (Nat.cast_sub (R := ℚ)
      (supportPolynomial_coeff_increasing i (by omega))).symm

theorem rootGVector_nonnegative (i : ℕ) (hi : i ≤ Fintype.card E / 2) :
    0 ≤ rootGVector (E := E) i := by
  rw [rootGVector_eq_support i hi]
  exact Nat.cast_nonneg _

noncomputable def rootTruncatedGVector (i : ℕ) : ℚ :=
  if i ≤ Fintype.card E / 2 then rootGVector (E := E) i else 0

theorem rootTruncatedGVector_eq_support (i : ℕ) :
    rootTruncatedGVector (E := E) i = (supportGVector (E := E) i : ℚ) := by
  by_cases hi : i ≤ Fintype.card E / 2
  · rw [rootTruncatedGVector, ite_eq_left hi, rootGVector_eq_support i hi]
  · rw [rootTruncatedGVector, ite_eq_right hi,
      supportGVector_eq_zero_of_large i (by omega), Nat.cast_zero]

theorem rootTruncatedGVector_nonnegative (i : ℕ) :
    0 ≤ rootTruncatedGVector (E := E) i := by
  rw [rootTruncatedGVector_eq_support]
  exact Nat.cast_nonneg _

end ResearchMain.PreorderGamma
