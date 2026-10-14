import MainTheorems.EulerianPencil.Recurrence

namespace ResearchMain.EulerianPencil

open Polynomial

theorem monomial_sum_natDegree_le (l : List (List ℕ)) (r : ℕ)
    (h : ∀ p ∈ l, descentCount p ≤ r) :
    ((l.map (fun p => (X : ℤ[X]) ^ descentCount p)).sum).natDegree ≤ r := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · simpa only [natDegree_X_pow] using h p List.mem_cons_self
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem eulerian_natDegree_le (n : ℕ) : (eulerian n).natDegree ≤ n - 1 := by
  apply monomial_sum_natDegree_le
  intro p hp
  have he : p.length = n := by
    simpa only [List.length_range] using (List.mem_permutations'.mp hp).length_eq
  cases p with
  | nil => simp [descentCount]
  | cons a l =>
    have hd := descentCount_prefix_le a l
    simp only [List.length_cons] at he
    omega

theorem coefficient_X_derivative (p : ℤ[X]) (k : ℕ) :
    (X * derivative p).coeff k = (k : ℤ) * p.coeff k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

theorem eulerian_coeff_step (n k : ℕ) :
    (eulerian (n + 1)).coeff (k + 1) =
      ((k : ℤ) + 2) * (eulerian n).coeff (k + 1) +
        ((n : ℤ) - k) * (eulerian n).coeff k := by
  rw [eulerian_recurrence]
  have he (p : ℤ[X]) : (1 + (n : ℤ[X]) * X) * p + X * (1 - X) * derivative p =
      p + (n : ℤ[X]) * (X * p) + X * derivative p - X * (X * derivative p) := by ring
  rw [he]
  simp only [coeff_sub, coeff_add, coeff_natCast_mul, coeff_X_mul, coeff_derivative,
    coefficient_X_derivative]
  ring

theorem eulerian_constant (n : ℕ) : (eulerian n).coeff 0 = 1 := by
  induction n with
  | zero => simp [eulerian_zero, coeff_one]
  | succ n ih =>
    rw [eulerian_recurrence]
    simp [mul_coeff_zero, ih]

theorem eulerian_top (n : ℕ) : (eulerian (n + 1)).coeff n = 1 := by
  induction n with
  | zero => simp [eulerian_one, coeff_one]
  | succ n ih =>
    rw [eulerian_coeff_step]
    have hz : (eulerian (n + 1)).coeff (n + 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h := eulerian_natDegree_le (n + 1)
      omega
    rw [hz, ih]
    push_cast
    ring

theorem eulerian_natDegree (n : ℕ) : (eulerian n).natDegree = n - 1 := by
  cases n with
  | zero => simp [eulerian_zero]
  | succ n =>
    apply natDegree_eq_of_le_of_coeff_ne_zero (eulerian_natDegree_le (n + 1))
    simpa only [Nat.add_sub_cancel, eulerian_top] using (show (1 : ℤ) ≠ 0 by norm_num)

theorem eulerian_monic (n : ℕ) : (eulerian n).Monic := by
  cases n with
  | zero => simp [eulerian_zero]
  | succ n =>
    apply monic_of_natDegree_le_of_coeff_eq_one n
    · simpa only [Nat.add_sub_cancel] using eulerian_natDegree_le (n + 1)
    · exact eulerian_top n

end ResearchMain.EulerianPencil
