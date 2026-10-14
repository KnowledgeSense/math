import MainTheorems.PreorderGamma.GammaExpansion
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace ResearchMain.PreorderGamma

open scoped BigOperators

noncomputable def gammaBasis (n k : ℕ) : Polynomial ℕ :=
  Polynomial.X ^ k * (1 + Polynomial.X) ^ (n - 2 * k)

theorem gammaBasis_coeff (n k i : ℕ) : (gammaBasis n k).coeff i =
    if k ≤ i then (n - 2 * k).choose (i - k) else 0 := by
  rw [gammaBasis, Polynomial.coeff_X_pow_mul']
  simp only [Polynomial.coeff_one_add_X_pow, Nat.cast_id]

theorem gammaBasis_coeff_symmetric (n k i : ℕ) (hk : 2 * k ≤ n) (hi : i ≤ n) :
    (gammaBasis n k).coeff i = (gammaBasis n k).coeff (n - i) := by
  rw [gammaBasis_coeff, gammaBasis_coeff]
  by_cases hki : k ≤ i
  · by_cases hkn : k ≤ n - i
    · simp only [ite_eq_left hki, ite_eq_left hkn]
      exact Nat.choose_symm_of_eq_add (by omega)
    · simp only [ite_eq_left hki, ite_eq_right hkn]
      exact Nat.choose_eq_zero_of_lt (by omega)
  · by_cases hkn : k ≤ n - i
    · simp only [ite_eq_right hki, ite_eq_left hkn]
      exact (Nat.choose_eq_zero_of_lt (by omega)).symm
    · simp only [ite_eq_right hki, ite_eq_right hkn]

theorem gammaBasis_coeff_increasing (n k i : ℕ) (hi : i < n / 2) :
    (gammaBasis n k).coeff i ≤ (gammaBasis n k).coeff (i + 1) := by
  rw [gammaBasis_coeff, gammaBasis_coeff]
  by_cases hki : k ≤ i
  · have hki' : k ≤ i + 1 := by omega
    have hshift : i + 1 - k = (i - k) + 1 := by omega
    simp only [ite_eq_left hki, ite_eq_left hki', hshift]
    exact Nat.choose_le_succ_of_lt_half_left (by omega)
  · simp only [ite_eq_right hki]
    exact Nat.zero_le _

theorem gammaBasis_g_coeff_zero_of_large (n k i : ℕ) (hk : i + 1 < k) :
    (gammaBasis n k).coeff (i + 1) - (gammaBasis n k).coeff i = 0 := by
  rw [gammaBasis_coeff, gammaBasis_coeff, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem gammaBasis_g_coeff_diagonal (n i : ℕ) :
    (gammaBasis n (i + 1)).coeff (i + 1) - (gammaBasis n (i + 1)).coeff i = 1 := by
  simp [gammaBasis_coeff]

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem supportPolynomial_coeff_gamma (i : ℕ) :
    (supportPolynomial (E := E)).coeff i =
      ∑ k ∈ Finset.range (Fintype.card E / 2 + 1),
        gammaCoefficient (E := E) k * (gammaBasis (Fintype.card E) k).coeff i := by
  rw [preorder_gamma_expansion]
  simp only [Polynomial.finsetSum_coeff, mul_assoc, Polynomial.coeff_C_mul, gammaBasis]

theorem supportPolynomial_coeff_zero : (supportPolynomial (E := E)).coeff 0 = 1 := by
  classical
  rw [supportPolynomial_coeff_gamma]
  rw [Finset.sum_eq_single 0]
  · simp [gammaBasis_coeff]
  · intro k hk hk₀
    simp [gammaBasis_coeff, hk₀]
  · simp

theorem supportPolynomial_coeff_symmetric (i : ℕ) (hi : i ≤ Fintype.card E) :
    (supportPolynomial (E := E)).coeff i =
      (supportPolynomial (E := E)).coeff (Fintype.card E - i) := by
  rw [supportPolynomial_coeff_gamma, supportPolynomial_coeff_gamma]
  apply Finset.sum_congr rfl
  intro k hk
  rw [gammaBasis_coeff_symmetric (Fintype.card E) k i (by
    have h := Finset.mem_range.mp hk
    omega) hi]

theorem supportPolynomial_coeff_top :
    (supportPolynomial (E := E)).coeff (Fintype.card E) = 1 := by
  rw [supportPolynomial_coeff_symmetric _ le_rfl, Nat.sub_self,
    supportPolynomial_coeff_zero]

theorem supportPolynomial_natDegree :
    (supportPolynomial (E := E)).natDegree = Fintype.card E := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [supportPolynomial_eq_preorderEnumerator]
    exact supportEnumerator_coeff_zero_of_large _ hi
  · rw [supportPolynomial_coeff_top]
    exact Nat.one_ne_zero

theorem supportPolynomial_monic : (supportPolynomial (E := E)).Monic := by
  change (supportPolynomial (E := E)).coeff (supportPolynomial (E := E)).natDegree = 1
  rw [supportPolynomial_natDegree, supportPolynomial_coeff_top]

theorem supportPolynomial_coeff_increasing (i : ℕ) (hi : i < Fintype.card E / 2) :
    (supportPolynomial (E := E)).coeff i ≤ (supportPolynomial (E := E)).coeff (i + 1) := by
  rw [supportPolynomial_coeff_gamma, supportPolynomial_coeff_gamma]
  apply Finset.sum_le_sum
  intro k hk
  exact Nat.mul_le_mul_left _ (gammaBasis_coeff_increasing (Fintype.card E) k i hi)

noncomputable def supportGVector (i : ℕ) : ℕ :=
  if i = 0 then (supportPolynomial (E := E)).coeff 0
  else (supportPolynomial (E := E)).coeff i - (supportPolynomial (E := E)).coeff (i - 1)

@[simp] theorem supportGVector_zero : supportGVector (E := E) 0 = 1 := by
  simp [supportGVector, supportPolynomial_coeff_zero]

omit [DecidableEq E] in
@[simp] theorem supportGVector_succ (i : ℕ) :
    supportGVector (E := E) (i + 1) =
      (supportPolynomial (E := E)).coeff (i + 1) - (supportPolynomial (E := E)).coeff i := by
  simp [supportGVector]

theorem supportPolynomial_g_coeff_gamma (i : ℕ) (hi : i < Fintype.card E / 2) :
    (supportPolynomial (E := E)).coeff (i + 1) - (supportPolynomial (E := E)).coeff i =
      ∑ k ∈ Finset.range (Fintype.card E / 2 + 1), gammaCoefficient (E := E) k *
        ((gammaBasis (Fintype.card E) k).coeff (i + 1) -
          (gammaBasis (Fintype.card E) k).coeff i) := by
  rw [supportPolynomial_coeff_gamma, supportPolynomial_coeff_gamma,
    ← Finset.sum_tsub_distrib _ (fun k _ => Nat.mul_le_mul_left
      (gammaCoefficient (E := E) k)
      (gammaBasis_coeff_increasing (Fintype.card E) k i hi))]
  apply Finset.sum_congr rfl
  intro k _
  exact (Nat.mul_sub_left_distrib _ _ _).symm

theorem supportGVector_succ_gamma (i : ℕ) (hi : i < Fintype.card E / 2) :
    supportGVector (E := E) (i + 1) =
      ∑ k ∈ Finset.range (Fintype.card E / 2 + 1), gammaCoefficient (E := E) k *
        ((gammaBasis (Fintype.card E) k).coeff (i + 1) -
          (gammaBasis (Fintype.card E) k).coeff i) := by
  rw [supportGVector_succ]
  exact supportPolynomial_g_coeff_gamma i hi

theorem supportPolynomial_coeff_decreasing (i : ℕ)
    (hlo : Fintype.card E / 2 ≤ i) (hhi : i < Fintype.card E) :
    (supportPolynomial (E := E)).coeff (i + 1) ≤ (supportPolynomial (E := E)).coeff i := by
  have hi : i ≤ Fintype.card E := by omega
  have hi' : i + 1 ≤ Fintype.card E := by omega
  rw [supportPolynomial_coeff_symmetric (i + 1) hi', supportPolynomial_coeff_symmetric i hi]
  by_cases hmid : Fintype.card E - (i + 1) < Fintype.card E / 2
  · have hnext : Fintype.card E - i = (Fintype.card E - (i + 1)) + 1 := by omega
    rw [hnext]
    exact supportPolynomial_coeff_increasing _ hmid
  · have heq : Fintype.card E - (i + 1) = i := by omega
    rw [heq]
    exact (supportPolynomial_coeff_symmetric i hi).le

theorem supportPolynomial_coeff_zero_of_large (i : ℕ) (hi : Fintype.card E < i) :
    (supportPolynomial (E := E)).coeff i = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rwa [supportPolynomial_natDegree]

theorem supportGVector_eq_zero_of_large (i : ℕ) (hi : Fintype.card E / 2 < i) :
    supportGVector (E := E) i = 0 := by
  cases i with
  | zero => omega
  | succ i =>
    rw [supportGVector_succ]
    by_cases hn : i < Fintype.card E
    · exact Nat.sub_eq_zero_of_le (supportPolynomial_coeff_decreasing i (by omega) hn)
    · rw [supportPolynomial_coeff_zero_of_large (i + 1) (by omega), Nat.zero_sub]

theorem preorder_support_palindromic_unimodal :
    (∀ i ≤ Fintype.card E, (supportPolynomial (E := E)).coeff i =
      (supportPolynomial (E := E)).coeff (Fintype.card E - i)) ∧
    (∀ i < Fintype.card E / 2, (supportPolynomial (E := E)).coeff i ≤
      (supportPolynomial (E := E)).coeff (i + 1)) ∧
    (∀ i, Fintype.card E / 2 ≤ i → i < Fintype.card E →
      (supportPolynomial (E := E)).coeff (i + 1) ≤ (supportPolynomial (E := E)).coeff i) :=
  ⟨supportPolynomial_coeff_symmetric, supportPolynomial_coeff_increasing,
    supportPolynomial_coeff_decreasing⟩

end ResearchMain.PreorderGamma
