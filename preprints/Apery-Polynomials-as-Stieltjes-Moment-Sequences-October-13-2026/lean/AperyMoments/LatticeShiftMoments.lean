import AperyMoments.LatticeMoments

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace AperyMoments

theorem sum_range_even_odd (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n + 1), f j) =
      (∑ j ∈ Finset.range (n + 1), f (2 * j)) + ∑ j ∈ Finset.range n, f (2 * j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ (f := fun j => f (2 * j)) (n + 1),
      Finset.sum_range_succ (f := fun j => f (2 * j + 1)) n]
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
    ring

theorem latticeShift_moment (n : ℕ) (u : ℝ) :
    (∫ c : ℝ, (c + u) ^ n * latticeDensity c) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * u ^ (n - j) *
        (∫ c : ℝ, c ^ j * latticeDensity c) := by
  have he : (fun c : ℝ => (c + u) ^ n * latticeDensity c) =
      (fun c => ∑ j ∈ Finset.range (n + 1), ((n.choose j : ℝ) * u ^ (n - j)) * (c ^ j * latticeDensity c)) := by
    funext c
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    exact integral_const_mul _ _
  · intro j _
    exact (latticePower_integrable j).const_mul _

theorem latticeShift_even_moment (n : ℕ) (u : ℝ) :
    (∫ c : ℝ, (c + u) ^ (2 * n) * latticeDensity c) =
      ∑ j ∈ Finset.range (n + 1), ((2 * n).choose (2 * j) : ℝ) *
        u ^ (2 * (n - j)) * (j.centralBinom : ℝ) ^ 2 := by
  rw [latticeShift_moment, sum_range_even_odd]
  have hodd : (∑ j ∈ Finset.range n, ((2 * n).choose (2 * j + 1) : ℝ) *
      u ^ (2 * n - (2 * j + 1)) * ∫ c : ℝ, c ^ (2 * j + 1) * latticeDensity c) = 0 := by
    simp only [latticeMoment_odd, mul_zero, Finset.sum_const_zero]
  rw [hodd, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [latticeMoment_even, Nat.mul_sub_left_distrib]

end AperyMoments
