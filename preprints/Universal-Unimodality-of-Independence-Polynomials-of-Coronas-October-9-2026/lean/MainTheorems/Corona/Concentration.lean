import MainTheorems.Corona.Moments

namespace ResearchMain.Corona

open Classical Polynomial

def NonnegativeCoefficients (p : ℝ[X]) : Prop := ∀ k, 0 ≤ p.coeff k

theorem NonnegativeCoefficients.mul {p q : ℝ[X]} (hp : NonnegativeCoefficients p)
    (hq : NonnegativeCoefficients q) : NonnegativeCoefficients (p * q) := by
  intro k
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun ij _ => mul_nonneg (hp ij.1) (hq ij.2))

theorem NonnegativeCoefficients.pow {p : ℝ[X]} (hp : NonnegativeCoefficients p) (n : ℕ) :
    NonnegativeCoefficients (p ^ n) := by
  induction n with
  | zero => simp only [pow_zero]; intro k; rw [coeff_one]; split_ifs <;> norm_num
  | succ n ih => rw [pow_succ]; exact ih.mul hp

theorem NonnegativeCoefficients.mass_nonnegative {p : ℝ[X]} (hp : NonnegativeCoefficients p) :
    0 ≤ mass p := by
  rw [mass_eq_sum]
  exact Finset.sum_nonneg (fun k _ => hp k)

theorem NonnegativeCoefficients.centeredSum_nonnegative {p : ℝ[X]}
    (hp : NonnegativeCoefficients p) (t : ℝ) : 0 ≤ centeredSum p t :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (hp k))

theorem variance_nonnegative {p : ℝ[X]} (hp : NonnegativeCoefficients p) (hm : 0 < mass p) :
    0 ≤ variance p := by
  have h := hp.centeredSum_nonnegative (mean p)
  rw [centeredSum_mean p (ne_of_gt hm)] at h
  exact (mul_nonneg_iff_of_pos_left hm).mp h

theorem mean_nonnegative {p : ℝ[X]} (hp : NonnegativeCoefficients p) (hm : 0 < mass p) :
    0 ≤ mean p := by
  unfold mean
  apply div_nonneg _ hm.le
  rw [firstMoment_eq_sum]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg k) (hp k))

theorem coefficient_le_mass {p : ℝ[X]} (hp : NonnegativeCoefficients p) (k : ℕ) :
    p.coeff k ≤ mass p := by
  by_cases hk : k ∈ p.support
  · rw [mass_eq_sum]
    exact Finset.single_le_sum (fun j _ => hp j) hk
  · rw [notMem_support_iff.mp hk]
    exact hp.mass_nonnegative

theorem secondMoment_bound {p : ℝ[X]} (hp : NonnegativeCoefficients p) {D : ℕ}
    (hD : p.natDegree ≤ D) : secondMoment p ≤ (D : ℝ) ^ 2 * mass p := by
  rw [secondMoment_eq_sum, mass_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkD : k ≤ D := (le_natDegree_of_ne_zero (mem_support_iff.mp hk)).trans hD
  have hcast : (k : ℝ) ≤ D := by exact_mod_cast hkD
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hD0 : (0 : ℝ) ≤ D := by positivity
  exact mul_le_mul_of_nonneg_right (by nlinarith only [hcast, hk0, hD0]) (hp k)

theorem variance_bound {p : ℝ[X]} (hp : NonnegativeCoefficients p) (hm : 0 < mass p) {D : ℕ}
    (hD : p.natDegree ≤ D) : variance p ≤ (D : ℝ) ^ 2 := by
  unfold variance
  have h := (div_le_iff₀ hm).mpr (secondMoment_bound hp hD)
  nlinarith only [h, sq_nonneg (mean p)]

theorem centeredSum_point {p : ℝ[X]} (hp : NonnegativeCoefficients p) (t : ℝ) (k : ℕ) :
    ((k : ℝ) - t) ^ 2 * p.coeff k ≤ centeredSum p t := by
  by_cases hk : k ∈ p.support
  · exact Finset.single_le_sum (fun (j : ℕ) _ => mul_nonneg (sq_nonneg ((j : ℝ) - t)) (hp j)) hk
  · have hz : p.coeff k = 0 := notMem_support_iff.mp hk
    rw [hz, mul_zero]
    exact hp.centeredSum_nonnegative t

theorem concentration_bound {p : ℝ[X]} (hp : NonnegativeCoefficients p) (T : Finset ℕ)
    (hT : T ⊆ p.support) {r t : ℝ} (hr : ∀ k ∈ T, r ^ 2 ≤ ((k : ℝ) - t) ^ 2) :
    r ^ 2 * (∑ k ∈ T, p.coeff k) ≤ centeredSum p t := by
  rw [Finset.mul_sum]
  apply (Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right (hr k hk) (hp k))).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg hT (fun k _ _ => mul_nonneg (sq_nonneg _) (hp k))

end ResearchMain.Corona
