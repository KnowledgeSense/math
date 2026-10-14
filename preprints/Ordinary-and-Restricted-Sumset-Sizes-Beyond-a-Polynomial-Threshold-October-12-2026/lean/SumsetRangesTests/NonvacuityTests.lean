import SumsetRangesTests.OriginalStatementTests
import Mathlib.Tactic.NormNum

open Finset SumsetRanges
namespace NonvacuityTests

-- These use kernel-reduced computations on actual finite sets.
theorem ordinary_three : ordinarySums ({0,1,3} : Finset ℤ) 2 = {0,1,2,3,4,6} := by decide
theorem restricted_three : restrictedSums ({0,1,3} : Finset ℤ) 2 = {1,3,4} := by decide
theorem ordinary_negatives : (ordinarySums ({-5,-2,4} : Finset ℤ) 3).card = 9 := by decide
theorem restricted_negatives : (restrictedSums ({-5,-2,4,7} : Finset ℤ) 2).card = 5 := by decide
theorem ordinary_zero_order : ordinarySums ({-7,2} : Finset ℤ) 0 = {0} := by decide
theorem restricted_empty_order : restrictedSums ({0,1} : Finset ℤ) 3 = ∅ := by decide
theorem excluded_four_six : excludedValues 4 6 = {22,23,26} := by decide
theorem excluded_three_three : excludedValues 3 3 = {8} := by decide
theorem excluded_two_empty : excludedValues 2 12 = ∅ := by decide
theorem excluded_card_two_empty : excludedValues 9 2 = ∅ := by decide

theorem normalized_example : ∃ B : Finset ℤ, ∃ d : ℕ,
    B.card = 3 ∧ (∀ q, (ordinarySums B q).card = (ordinarySums ({-9,-5,3} : Finset ℤ) q).card) ∧
    0 ∈ B ∧ (d : ℤ) ∈ B ∧ (∀ b ∈ B, 0 ≤ b ∧ b ≤ d) ∧ B.gcd id = 1 := by
  simpa using exists_ordinary_normalization ({-9,-5,3} : Finset ℤ) (by decide)

theorem lev_example : (ordinarySums ({0,2,5} : Finset ℤ) 2).card + 4 ≤
    (ordinarySums ({0,2,5} : Finset ℤ) 3).card := by
  exact lev_growth {0,2,5} 5 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem forbidden_eight : ¬ ∃ A : Finset ℤ, A.card = 3 ∧ (ordinarySums A 3).card = 8 := by
  intro h
  exact ordinaryRange_not_mem_excludedValues h (by decide)

theorem forbidden_twenty_six : ¬ ∃ A : Finset ℤ, A.card = 6 ∧ (ordinarySums A 4).card = 26 := by
  intro h
  exact ordinaryRange_not_mem_excludedValues h (by decide)

theorem threshold_nonempty : ∃ h k : ℕ, 3 ≤ h ∧ 2 ≤ h ∧ (2*h)^80 ≤ k :=
  ⟨3,6^80,by decide,by decide,by decide⟩

theorem restricted_at_threshold : ∃ A : Finset ℤ,
    A.card = 6^80 ∧ (∀ a ∈ A, 0 ≤ a ∧ a ≤ ((6^80)^restrictedExponent 3 : ℕ)) ∧
    (restrictedSums A 3).card = 3*(6^80-3)+1 := by
  apply restricted_interval_realized 3 (6^80) (3*(6^80-3)+1) (by decide) (by decide) (by omega)
  have hc := Nat.choose_succ_right_eq (6^80) 2
  norm_num [Nat.choose_two_right] at hc ⊢
  omega

theorem ordinary_at_threshold : ∃ A : Finset ℤ,
    A.card = 6^80 ∧ (∀ a ∈ A, 0 ≤ a ∧ a ≤ ((6^80)^ordinaryExponent 3 : ℕ)) ∧
    (ordinarySums A 3).card = 3*6^80-2 := by
  apply ordinary_interval_realized 3 (6^80) (3*6^80-2) (by decide) (by decide)
  · norm_num [ordinaryMinimum]
  · have hc := Nat.choose_succ_right_eq (3+6^80-1) 2
    norm_num [Nat.choose_two_right] at hc ⊢
    omega
  · decide

theorem ordinary_h_two_at_threshold : ∃ A : Finset ℤ,
    A.card = 4^80 ∧ (∀ a ∈ A, 0 ≤ a ∧ a ≤ ((4^80)^ordinaryExponent 2 : ℕ)) ∧
    (ordinarySums A 2).card = 2*4^80-1 := by
  apply ordinary_interval_realized 2 (4^80) (2*4^80-1) (by decide) (by decide)
  · norm_num [ordinaryMinimum]
  · norm_num [Nat.choose_two_right]
  · simp [excludedValues]

#print axioms ordinary_three
#print axioms restricted_three
#print axioms ordinary_negatives
#print axioms restricted_negatives
#print axioms ordinary_zero_order
#print axioms restricted_empty_order
#print axioms excluded_four_six
#print axioms excluded_three_three
#print axioms excluded_two_empty
#print axioms excluded_card_two_empty
#print axioms normalized_example
#print axioms lev_example
#print axioms forbidden_eight
#print axioms forbidden_twenty_six
#print axioms threshold_nonempty
#print axioms restricted_at_threshold
#print axioms ordinary_at_threshold
#print axioms ordinary_h_two_at_threshold

theorem restricted_maximum_at_threshold : ∃ A : Finset ℤ,
    A.card = 6^80 ∧ (∀ a ∈ A, 0 ≤ a ∧ a ≤ ((6^80)^restrictedExponent 3 : ℕ)) ∧
    (restrictedSums A 3).card = (6^80).choose 3 := by
  have hlo : 3*(6^80-3)+1 ≤ (6^80).choose 3 := by
    have hc := Nat.choose_succ_right_eq (6^80) 2
    norm_num [Nat.choose_two_right] at hc ⊢
    omega
  exact restricted_interval_realized 3 (6^80) ((6^80).choose 3) (by decide) (by decide) hlo le_rfl

theorem ordinary_maximum_at_threshold : ∃ A : Finset ℤ,
    A.card = 6^80 ∧ (∀ a ∈ A, 0 ≤ a ∧ a ≤ ((6^80)^ordinaryExponent 3 : ℕ)) ∧
    (ordinarySums A 3).card = (3+6^80-1).choose 3 := by
  have hc := Nat.choose_succ_right_eq (3+6^80-1) 2
  have hlo : ordinaryMinimum 3 (6^80) ≤ (3+6^80-1).choose 3 := by
    norm_num [ordinaryMinimum, Nat.choose_two_right] at hc ⊢
    omega
  have hex : (3+6^80-1).choose 3 ∉ excludedValues 3 (6^80) := by
    norm_num [excludedValues, ordinaryMinimum, Finset.range_one, Nat.choose_two_right] at hc ⊢
    omega
  exact ordinary_interval_realized 3 (6^80) ((3+6^80-1).choose 3) (by decide) (by decide) hlo le_rfl hex

theorem lev_nontrivial_stabilizer_example :
    (ordinarySums ({0,1,6,7,12} : Finset ℤ) 1).card + 7 ≤
      (ordinarySums ({0,1,6,7,12} : Finset ℤ) 2).card := by
  exact lev_growth {0,1,6,7,12} 12 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem quotient_nontrivial_stabilizer :
    (ordinarySums ({0,1,6,7} : Finset (ZMod 12)) 2).card = 6 ∧
    (ordinarySums ({0,1,6,7} : Finset (ZMod 12)) 2).addStab.card = 2 := by
  decide

#print axioms restricted_maximum_at_threshold
#print axioms ordinary_maximum_at_threshold
#print axioms lev_nontrivial_stabilizer_example
#print axioms quotient_nontrivial_stabilizer

end NonvacuityTests
