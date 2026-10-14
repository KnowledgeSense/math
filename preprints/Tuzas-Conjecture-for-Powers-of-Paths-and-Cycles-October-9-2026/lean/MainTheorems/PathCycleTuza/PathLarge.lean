import MainTheorems.PathCycleTuza.PathMass
import MainTheorems.PathCycleTuza.PathParity
import MainTheorems.PathCycleTuza.PathArithmetic

namespace ResearchMain.PathCycleTuza

open Tuza

theorem path_cover_integer (n k : ℕ) (hn : k + 1 ≤ n) :
    (coverNumber (pathPower n k) : ℤ) ≤
      ((k / 2 : ℕ) : ℤ) * ((n : ℤ) - (k / 2 : ℕ) - 1) := by
  have h : (coverNumber (pathPower n k) : ℤ) ≤ ((k / 2 * (n - k / 2 - 1) : ℕ) : ℤ) :=
    by exact_mod_cast path_parity_cover n k hn
  rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one] at h
  exact h

theorem path_large_inequality (n k : ℕ) (hk : 7 ≤ k) (hn : 2 * k + 2 ≤ n)
    (he₈ : k ≠ 8) (he₉ : k ≠ 9) : Inequality (pathPower n k) := by
  obtain ⟨m, hm, ha⟩ := path_exponent_arithmetic k n hk hn he₈ he₉
  have hp := skolem_path_bound_of_le n k m hm (by omega)
  have hc := path_cover_integer n k (by omega)
  have hi : (coverNumber (pathPower n k) : ℤ) ≤ 2 * packingNumber (pathPower n k) := by
    nlinarith
  exact_mod_cast hi

theorem path_three_to_five (n k : ℕ) (hk : 3 ≤ k) (hkb : k ≤ 5) : Inequality (pathPower n k) := by
  by_cases hn : n ≤ k + 1
  · rw [pathPower_complete n k hn]
    exact complete_inequality n
  · have hm : 3 * 1 + hookFlag 1 ≤ k := by simp [hookFlag]; omega
    have hp := skolem_path_bound_of_le n k 1 hm (by omega)
    have hc := path_cover_integer n k (by omega)
    have hn' : (k : ℤ) + 1 < n := by exact_mod_cast Nat.lt_of_not_ge hn
    have hi : (coverNumber (pathPower n k) : ℤ) ≤ 2 * packingNumber (pathPower n k) := by
      interval_cases k <;> norm_num [hookFlag] at * <;> nlinarith
    exact_mod_cast hi

theorem path_zero_inequality (n : ℕ) : Inequality (pathPower n 0) := by
  rw [pathPower_zero]
  exact bottom_inequality _

theorem path_one_inequality (n : ℕ) : Inequality (pathPower n 1) :=
  triangleFree_inequality _ (pathPower_one_triangleFree n)

end ResearchMain.PathCycleTuza
