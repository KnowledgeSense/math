import BoseBurton.FlagCountingCard
import BoseBurton.RestrictedZ

noncomputable section
namespace BoseBurton
open Submodule Module Finset Polynomial
open scoped Classical

theorem gaussian_flag_above_one (q : ℝ) (hq : 1 < q)
    (n k l : ℕ) (hlk : l ≤ k) :
    gaussian q n l * gaussian q (n-l) (k-l) = gaussian q n k * gaussian q k l := by
  by_cases hkn : k ≤ n
  · have hp (i : ℕ) := qFactorial_ne_zero_above_one q hq i
    simp only [gaussian, show l ≤ n by omega, hlk, hkn,
      show k-l ≤ n-l by omega, ite_true, show n-l-(k-l)=n-k by omega]
    field_simp [hp]
  · by_cases hln : l ≤ n
    · rw [gaussian_outside q n k (by omega), gaussian_outside q (n-l) (k-l) (by omega)]
      ring
    · rw [gaussian_outside q n k (by omega), gaussian_outside q n l (by omega)]
      ring

theorem gaussian_max_reflection (q : ℝ) (d i : ℕ) (hi : i ≤ d) :
    gaussian q d (max i (d-i)) = gaussian q d i := by
  by_cases h : d-i ≤ i
  · rw [max_eq_left h]
  · rw [max_eq_right (by omega), gaussian_symm q d i hi]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Module.Finite K V] [Finite V]

theorem rankEnumerator_coeff_real (i : ℕ) :
    ((projectiveRankEnumerator K V).coeff i : ℝ) =
      gaussian (Fintype.card K : ℝ) (finrank K V) i := by
  rw [projectiveRankEnumerator_coeff]
  norm_cast
  exact subspace_count_gaussian_all K V i

theorem restrictedZRow_coeff_rank (W U : Submodule K V) (i : ℕ) (hi : i ≤ finrank K U) :
    ((restrictedZRow W U).coeff i : ℝ) = gaussian (Fintype.card K : ℝ) (finrank K U) i -
      (Nat.card {S : Submodule K (W.comap U.subtype) // finrank K S = max i (finrank K U-i)} : ℝ) := by
  rw [restrictedZRow_coeff, ite_eq_left hi, Int.cast_sub, rankEnumerator_coeff_real,
    projectiveRankEnumerator_coeff]
  norm_cast

/-- Flag-pair cancellation gives the exact source whole-flat coefficient identity. -/
theorem summed_restrictedZ_coeff (W : Submodule K V) (d i : ℕ) (hi : i ≤ d) :
    (∑ U : NondeletedRankSubspace W d, ((restrictedZRow W U.1).coeff i : ℝ)) =
      gaussian (Fintype.card K : ℝ) (finrank K V) d * gaussian (Fintype.card K : ℝ) d i -
      gaussian (Fintype.card K : ℝ) (finrank K W) (max i (d-i)) *
        gaussian (Fintype.card K : ℝ) (finrank K V-max i (d-i)) (d-max i (d-i)) := by
  have hs : (∑ U : NondeletedRankSubspace W d, ((restrictedZRow W U.1).coeff i : ℝ)) =
      (Nat.card (NondeletedRankSubspace W d) : ℝ)*gaussian (Fintype.card K : ℝ) d i -
      ∑ U : NondeletedRankSubspace W d,
        (Nat.card {S : Submodule K (W.comap U.1.subtype) // finrank K S = max i (d-i)} : ℝ) := by
    calc
      _ = ∑ U : NondeletedRankSubspace W d,
          (gaussian (Fintype.card K : ℝ) d i -
            (Nat.card {S : Submodule K (W.comap U.1.subtype) // finrank K S = max i (d-i)} : ℝ)) := by
        apply sum_congr rfl
        intro U _
        rw [restrictedZRow_coeff_rank W U.1 i (by rw [U.2.1]; exact hi), U.2.1]
      _ = _ := by rw [sum_sub_distrib, sum_const, nsmul_eq_mul, card_univ, Nat.card_eq_fintype_card]
  rw [hs, nondeleted_rank_count W d, flag_pair_gaussian W d (max i (d-i)) (by omega)]
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hf := gaussian_flag_above_one (Fintype.card K : ℝ) hq
    (finrank K W) d (max i (d-i)) (by omega)
  rw [gaussian_max_reflection _ d i hi] at hf
  linear_combination hf

end BoseBurton
