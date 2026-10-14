import Paving.FullCoefficientBridge
import Paving.Support

namespace Paving
open MatroidInverseZ
variable {α : Type*} [Fintype α]

/-- Positivity of every actual coefficient in every paving rank at least three. -/
theorem IsPaving.coefficient_pos_higher {M : Matroid α} (hM : IsPaving M)
    (hr : 3≤rank M) (k : ℕ) (hk : k≤rank M) : 0 < (matroidInverseZ M).coeff k := by
  have hB := normalization_positive M
  by_cases he : rank M%2=0
  · have hm : 2≤rank M/2 := by omega
    have hpar : rank M=2*(rank M/2) := by omega
    have h := hM.actual_even_positive (rank M/2) hm hpar k (by omega)
    have hc := hM.actual_coefficient_even (rank M/2) hm hpar k (by omega)
    have hp : (0:ℝ) < ((matroidInverseZ M).coeff k:ℝ) := by rw [hc]; exact mul_pos hB h
    exact_mod_cast hp
  · have hm : 1≤rank M/2 := by omega
    have hpar : rank M=2*(rank M/2)+1 := by omega
    have h := hM.actual_odd_positive (rank M/2) hm hpar k
    have hc := hM.actual_coefficient_odd (rank M/2) hm hpar k hk
    have hp : (0:ℝ) < ((matroidInverseZ M).coeff k:ℝ) := by rw [hc]; exact mul_pos hB h
    exact_mod_cast hp

theorem positive_scaling_strict {B a b c : ℝ} (hB : 0<B) (h : a*c<b^2) :
    (B*a)*(B*c)<(B*b)^2 := by
  have hh := mul_lt_mul_of_pos_left h (sq_pos_of_pos hB)
  convert hh using 1 <;> ring

theorem IsPaving.coefficient_strict_higher {M : Matroid α} (hM : IsPaving M)
    (hr : 3≤rank M) (k : ℕ) (hk : 1≤k) (hkr : k<rank M) :
    (matroidInverseZ M).coeff (k-1)*(matroidInverseZ M).coeff (k+1) <
      (matroidInverseZ M).coeff k^2 := by
  have hB := normalization_positive M
  by_cases he : rank M%2=0
  · have hm : 2≤rank M/2 := by omega
    have hpar : rank M=2*(rank M/2) := by omega
    have h := positive_scaling_strict hB (hM.actual_even_strict (rank M/2) hm hpar k hk (by omega))
    rw [← hM.actual_coefficient_even (rank M/2) hm hpar (k-1) (by omega),
      ← hM.actual_coefficient_even (rank M/2) hm hpar (k+1) (by omega),
      ← hM.actual_coefficient_even (rank M/2) hm hpar k (by omega)] at h
    exact_mod_cast h
  · have hm : 1≤rank M/2 := by omega
    have hpar : rank M=2*(rank M/2)+1 := by omega
    have h := positive_scaling_strict hB (hM.actual_odd_strict (rank M/2) hm hpar k hk hkr)
    rw [← hM.actual_coefficient_odd (rank M/2) hm hpar (k-1) (by omega),
      ← hM.actual_coefficient_odd (rank M/2) hm hpar (k+1) (by omega),
      ← hM.actual_coefficient_odd (rank M/2) hm hpar k (by omega)] at h
    exact_mod_cast h

/-- The complete higher-rank theorem, including the free and coloop boundaries. -/
theorem paving_inverseZ_higher_main (M : Matroid α) (hM : IsPaving M) (hr : 3≤rank M) :
    (matroidInverseZ M).natDegree=rank M ∧
    (∀ k≤rank M, 0 < (matroidInverseZ M).coeff k) ∧
    (∀ k≤rank M, (matroidInverseZ M).coeff (rank M-k)=(matroidInverseZ M).coeff k) ∧
    (∀ k, 1≤k → k<rank M →
      (matroidInverseZ M).coeff (k-1)*(matroidInverseZ M).coeff (k+1)<
        (matroidInverseZ M).coeff k^2) := by
  refine ⟨?_,fun k hk => hM.coefficient_pos_higher hr k hk,
    fun k hk => (actual_inverseZ_coeff_symm M k hk).symm,
    fun k hk hkr => hM.coefficient_strict_higher hr k hk hkr⟩
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (actual_inverseZ_degree_le M)
    (ne_of_gt (hM.coefficient_pos_higher hr (rank M) le_rfl))

end Paving
