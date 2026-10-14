import ArithmeticSections

open ArithmeticSections MeasureTheory
open scoped Topology

example (W : Set ℝ)
    (hW : W ∈ 𝓝 ((4 * Real.pi / 3) * Real.tan (Real.pi * (4 + Real.sqrt 2) / 14) ^ 3)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ arithmeticSet ∩ W ∧ 0 < volume E :=
  positive_measure_in_every_neighborhood hW

example : 0 < volume arithmeticSet := arithmeticSet_positive_volume

example : MeasurableSet arithmeticSet := measurableSet_arithmeticSet

example : seedVolume ∈ arithmeticSet := seedVolume_mem_arithmeticSet

example (A : ℝ) : A ∈ arithmeticSet ↔
    8 * (4 * Real.pi / 3) < A ∧
      Irrational (Real.arctan ((A / (4 * Real.pi / 3)) ^ (1 / 3 : ℝ)) / Real.pi) ∧
      ∀ k : ℕ, 2 ≤ k →
        max (minusDeviation (Real.arctan ((A / (4 * Real.pi / 3)) ^ (1 / 3 : ℝ)) / Real.pi) k)
          (plusDeviation (Real.arctan ((A / (4 * Real.pi / 3)) ^ (1 / 3 : ℝ)) / Real.pi) k) <
        oddDistance (Real.arctan ((A / (4 * Real.pi / 3)) ^ (1 / 3 : ℝ)) / Real.pi) (k + 1) := by
  simp only [arithmeticSet, Set.mem_ofPred_eq, omegaThree, rotationOfVolume, conditionGap,
    sub_pos]

example (k : ℕ) (hk : 2 ≤ k) : 0 < conditionGap seedRotation k := seed_all_conditions k hk

example (γ : ℝ) (hγ : Irrational γ) (hlo : 1 / 3 < γ) (hhi : γ < 1 / 2)
    (hdigits : ∀ l, 257 ≤ l → actualDigit (2 * γ) l ≤ l ^ 2)
    (k : ℕ) (hk : actualDenominator (2 * γ) 256 ≤ k) : 0 < conditionGap γ k :=
  polynomial_digit_tail hγ hlo hhi hdigits hk

example (b : ℕ → ℕ) (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ) :
    digitCylinder b (n + 1) = cylinderInterval b n 1 :=
  digitCylinder_eq_cylinderInterval hb n
