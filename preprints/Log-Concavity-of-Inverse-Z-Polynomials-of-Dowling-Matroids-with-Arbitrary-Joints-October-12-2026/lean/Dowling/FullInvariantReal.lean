import Dowling.FullZGeneratingFunction
import Dowling.ReciprocalUniqueness

noncomputable section
namespace Dowling
open Polynomial PowerSeries
open scoped Classical BigOperators
variable {G : Type*} [Group G] [Fintype G]

theorem fullP_natDegree_le (n : ℕ) : (fullP G n).natDegree ≤ n := by
  cases n with
  | zero => simp
  | succ n =>
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    exact fullP_high_coeff _ j (by omega) (by omega)

theorem fullZ_natDegree_le (n : ℕ) : (fullZ G n).natDegree ≤ n := by
  rw [fullZ_sum_partitions]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro p _
  have hp := p.roots_card_le
  calc
    _ ≤ (Polynomial.X^(n-p.roots.card) : Polynomial ℤ).natDegree + (fullP G p.roots.card).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (n-p.roots.card)+p.roots.card := by
      rw [Polynomial.natDegree_X_pow]
      exact Nat.add_le_add_left (fullP_natDegree_le _) _
    _ = n := Nat.sub_add_cancel hp

theorem fullPSeries_high_coeff (n k : ℕ) (hn : 0 < n) (hk : n ≤ 2*k) :
    (PowerSeries.coeff n (fullPSeries G)).coeff k = 0 := by
  rw [fullPSeries,invariantEGF_coeff,Polynomial.coeff_C_mul,Polynomial.coeff_map,
    fullP_high_coeff n k hn hk,map_zero,mul_zero]

theorem fullZSeries_coeff_symm (n k : ℕ) (hk : k ≤ n) :
    (PowerSeries.coeff n (fullZSeries G)).coeff k =
      (PowerSeries.coeff n (fullZSeries G)).coeff (n-k) := by
  rw [fullZSeries,invariantEGF_coeff]
  simp only [Polynomial.coeff_C_mul,Polynomial.coeff_map,fullZ_coeff_symm n k hk]

theorem fullZSeries_coeff_natDegree_le (n : ℕ) :
    (PowerSeries.coeff n (fullZSeries G)).natDegree ≤ n := by
  rw [fullZSeries,invariantEGF_coeff]
  calc
    _ ≤ (Polynomial.C ((n.factorial:ℝ)⁻¹)).natDegree +
      ((fullZ G n).map (Int.castRingHom ℝ)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ n := by
      rw [Polynomial.natDegree_C,zero_add]
      exact Polynomial.natDegree_map_le.trans (fullZ_natDegree_le n)

theorem fullZSeries_coeff_reciprocal (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    t^n*(PowerSeries.coeff n (fullZSeries G)).eval t⁻¹ =
      (PowerSeries.coeff n (fullZSeries G)).eval t := by
  have hr : Polynomial.reflect n (PowerSeries.coeff n (fullZSeries G)) =
      PowerSeries.coeff n (fullZSeries G) := by
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_reflect]
    by_cases hk : k ≤ n
    · rw [Polynomial.revAt_le hk,fullZSeries_coeff_symm n k hk]
    · rw [Polynomial.revAt_eq_self_of_lt (by omega)]
  rw [← eval_reflect_nonzero _ n (fullZSeries_coeff_natDegree_le n) t ht,hr]

end Dowling
