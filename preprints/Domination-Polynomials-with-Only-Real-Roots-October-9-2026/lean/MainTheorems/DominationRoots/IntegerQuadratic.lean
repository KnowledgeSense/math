import MainTheorems.DominationRoots.AuxiliaryInequality
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Minpoly.Field

namespace ResearchMain.DominationRoots

open Polynomial

noncomputable def quadraticPolynomial : ℤ[X] := X ^ 2 - C 3 * X + 1

theorem quadraticPolynomial_degree : quadraticPolynomial.degree = 2 := by
  unfold quadraticPolynomial
  compute_degree <;> norm_num

theorem quadraticPolynomial_natDegree : quadraticPolynomial.natDegree = 2 :=
  natDegree_eq_of_degree_eq_some quadraticPolynomial_degree

theorem quadraticPolynomial_monic : quadraticPolynomial.Monic := by
  apply monic_of_degree_le 2 quadraticPolynomial_degree.le
  norm_num [quadraticPolynomial, coeff_C_mul, coeff_X, coeff_one]

theorem quadraticPolynomial_no_integer_root (z : ℤ) :
    ¬quadraticPolynomial.IsRoot z := by
  intro hz
  have he : z ^ 2 - 3 * z + 1 = 0 := by
    simpa [Polynomial.IsRoot, quadraticPolynomial] using hz
  by_cases h0 : z ≤ 0
  · nlinarith [sq_nonneg z]
  by_cases h3 : 3 ≤ z
  · nlinarith [mul_nonneg (show 0 ≤ z by omega) (sub_nonneg.mpr h3)]
  have h12 : z = 1 ∨ z = 2 := by omega
  rcases h12 with rfl | rfl <;> norm_num at he

theorem quadraticPolynomial_irreducible : Irreducible quadraticPolynomial := by
  apply (quadraticPolynomial_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [quadraticPolynomial_natDegree]) (by rw [quadraticPolynomial_natDegree]; omega)).mpr
  apply Multiset.eq_zero_of_forall_notMem
  intro z hz
  exact quadraticPolynomial_no_integer_root z
    ((mem_roots quadraticPolynomial_monic.ne_zero).mp hz)

theorem quadraticPolynomial_aeval (x : ℝ) :
    (aeval x) quadraticPolynomial = quadratic 3 1 x := by
  norm_num [quadraticPolynomial, quadratic, map_ofNat]

theorem quadraticPolynomial_dvd_of_root {f : ℤ[X]} {x : ℝ}
    (hf : (aeval x) f = 0) (hx : quadratic 3 1 x = 0) : quadraticPolynomial ∣ f := by
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  have hi : Irreducible (quadraticPolynomial.map φ) :=
    (quadraticPolynomial_monic.irreducible_iff_irreducible_map_fraction_map
      (K := ℚ)).mp quadraticPolynomial_irreducible
  have hquad : (aeval x) (quadraticPolynomial.map φ) = 0 := by
    norm_num [φ, quadraticPolynomial, quadratic, map_ofNat] at *
    exact hx
  have hf' : (aeval x) (f.map φ) = 0 := by
    change (aeval x) (f.map (algebraMap ℤ ℚ)) = 0
    rw [aeval_map_algebraMap]
    exact hf
  exact (map_dvd_map φ Int.cast_injective quadraticPolynomial_monic).mp
    ((hi.dvd_iff_aeval_eq_zero hquad).mp hf')

end ResearchMain.DominationRoots
