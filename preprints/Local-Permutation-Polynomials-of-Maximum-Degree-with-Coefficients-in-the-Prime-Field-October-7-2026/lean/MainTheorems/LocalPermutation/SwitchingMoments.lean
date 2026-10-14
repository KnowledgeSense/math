import MainTheorems.LocalPermutation.Switching

namespace ResearchMain.LocalPermutation

open Classical

variable {K : Type} [Field K] [Fintype K]

omit [Fintype K] in
theorem product_weighted_coordinate {n : ℕ} (h : K → K) (x : Fin n → K) (i : Fin n) :
    h (x i) * (∏ j, x j) = ∏ j, if j = i then h (x j) * x j else x j := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => x j) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => if j = i then h (x j) * x j else x j) (Finset.mem_univ i)]
  simp only [ite_true, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.mem_erase.mp hj).1]

theorem coordinate_moment_zero (hq : 2 < Fintype.card K) {n : ℕ} (hn : 2 ≤ n)
    (h : K → K) (i : Fin n) : (∑ x : Fin n → K, h (x i) * ∏ j, x j) = 0 := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hj⟩ := exists_ne i
  simp_rw [product_weighted_coordinate]
  rw [← Fintype.prod_sum (fun j (a : K) => if j = i then h a * a else a)]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp only [ite_eq_right hj]
  simpa only [pow_one] using FiniteField.sum_pow_lt_card_sub_one K 1 (by omega)

theorem switchFunction_moment (hq : 2 < Fintype.card K) {n : ℕ} (hn : 2 ≤ n)
    (T : Finset K) (h : Equiv.Perm K) : weightedMoment (switchFunction (n := n) T h) = (∑ a ∈ T, a) ^ n := by
  have hfirst : (∑ x : Fin n → K, (∑ i, h (x i)) * ∏ j, x j) = 0 := by
    calc
      _ = ∑ i : Fin n, ∑ x : Fin n → K, h (x i) * ∏ j, x j := by
        simp_rw [Finset.sum_mul]
        exact Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero (fun i _ => coordinate_moment_zero hq hn h i)
  have hsecond : (∑ x : Fin n → K, (∏ i, setIndicator T (x i)) * ∏ j, x j) = (∑ a ∈ T, a) ^ n := by
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun _i : Fin n => fun a : K => setIndicator T a * a)]
    simp_rw [setIndicator_sum]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold weightedMoment switchFunction
  simp only [add_mul, Finset.sum_add_distrib, hfirst, hsecond, zero_add]

theorem switching_maximum_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hq : 2 < Fintype.card K) {n : ℕ} (hn : 2 ≤ n) (S T : Finset K) (h : Equiv.Perm K)
    (himage : ∀ a, a ∈ T ↔ h a ∈ S) (hshift : ∀ a ∈ S, a + 1 ∈ S)
    (hT : ∀ a, a ^ p ∈ T ↔ a ∈ T) (hh : ∀ a, h (a ^ p) = h a ^ p)
    (hsum : (∑ a ∈ T, a) ≠ 0) : ∃ P : MvPolynomial (Fin n) K,
      PrimeCoefficients P ∧ IsLocalPermutation (fun x => MvPolynomial.eval x P) ∧
      (∀ i, P.degreeOf i ≤ Fintype.card K - 2) ∧ P.totalDegree = n * (Fintype.card K - 2) := by
  apply exists_maximum_degree p hq (switchFunction_localPermutation S T h himage hshift)
    (switchFunction_frobenius p T h hT hh)
  rw [switchFunction_moment hq hn]
  exact pow_ne_zero n hsum

end ResearchMain.LocalPermutation
