import RandomWalkSearch.TrajectoryRanges
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # The actual iid lazy law and its integrated finite-horizon range

Uniform finite-prefix probabilities characterize independent uniform four-symbol
increments. The law is imposed on tapes, not on ranges or on algorithm success.
-/

namespace RandomWalkSearch
open MeasureTheory
open scoped ENNReal BigOperators

variable {Ω F : Type*} [MeasurableSpace Ω] [Fintype F]

/-- Integrating a function of a genuinely uniform finite random variable. -/
theorem lintegral_uniform_finite (μ : Measure Ω) (f : Ω → F)
    (hmeas : ∀ x, MeasurableSet {ω | f ω = x})
    (hlaw : ∀ x, μ {ω | f ω = x} = (Fintype.card F : ℝ≥0∞)⁻¹)
    (g : F → ℝ≥0∞) :
    (∫⁻ ω, g (f ω) ∂μ) = (∑ x, g x) / Fintype.card F := by
  classical
  have hrep : (fun ω => g (f ω)) =
      fun ω => ∑ x : F, Set.indicator {ω | f ω = x} (fun _ => g x) ω := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [Finset.sum_eq_single (f ω)]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  rw [hrep, lintegral_finsetSum _ (fun x _ => measurable_const.indicator (hmeas x))]
  simp_rw [lintegral_indicator (hmeas _), setLIntegral_const, hlaw]
  simp [div_eq_mul_inv, Finset.sum_mul]

/-- The natural-valued specialization written as an ordinary finite expectation. -/
theorem lintegral_uniform_nat [Nonempty F] (μ : Measure Ω) (f : Ω → F)
    (hmeas : ∀ x, MeasurableSet {ω | f ω = x})
    (hlaw : ∀ x, μ {ω | f ω = x} = (Fintype.card F : ℝ≥0∞)⁻¹)
    (g : F → ℕ) :
    (∫⁻ ω, (g (f ω) : ℝ≥0∞) ∂μ) = ENNReal.ofReal (𝔼 x, (g x : ℝ)) := by
  rw [lintegral_uniform_finite μ f hmeas hlaw (fun x => (g x : ℝ≥0∞))]
  rw [Fintype.expect_eq_sum_div_card, ENNReal.ofReal_div_of_pos (by positivity)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => Nat.cast_nonneg (g x))]
  simp

namespace Cycle
variable {k : ℕ}

/-- Every trajectory uses an actual iid lazy tape. This assumption contains
only measurable cylinder events and their exact probabilities. -/
def Randomized.LazyLaw (A : Randomized k Ω) (μ : Measure Ω) : Prop :=
  ∀ i T (t : LazyWalk.Tape T),
    MeasurableSet {ω | LazyWalk.prefixTape T (A.increments ω i) = t} ∧
    μ {ω | LazyWalk.prefixTape T (A.increments ω i) = t} =
      (Fintype.card (LazyWalk.Tape T) : ℝ≥0∞)⁻¹

theorem Randomized.lintegral_range (A : Randomized k Ω) (μ : Measure Ω)
    (hlaw : A.LazyLaw μ) (i T : ℕ) :
    (∫⁻ ω, (LazyWalk.integerRange T (LazyWalk.prefixTape T (A.increments ω i)) : ℝ≥0∞) ∂μ) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * (T : ℝ))) := by
  rw [lintegral_uniform_nat μ (fun ω => LazyWalk.prefixTape T (A.increments ω i))
    (fun t => (hlaw i T t).1) (fun t => (hlaw i T t).2)]
  exact ENNReal.ofReal_le_ofReal (LazyWalk.integerRange_expect_le T)

theorem Randomized.measurable_range (A : Randomized k Ω) (μ : Measure Ω)
    (hlaw : A.LazyLaw μ) (i T : ℕ) :
    Measurable fun ω => (LazyWalk.integerRange T (LazyWalk.prefixTape T (A.increments ω i)) : ℝ≥0∞) := by
  classical
  let f := fun ω => LazyWalk.prefixTape T (A.increments ω i)
  have hrep : (fun ω => (LazyWalk.integerRange T (f ω) : ℝ≥0∞)) =
      fun ω => ∑ t : LazyWalk.Tape T,
        Set.indicator {ω | f ω = t} (fun _ => (LazyWalk.integerRange T t : ℝ≥0∞)) ω := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [Finset.sum_eq_single (f ω)]
    · simp
    · intro t _ ht
      simp [Ne.symm ht]
    · simp
  rw [hrep]
  exact Finset.measurable_sum _ (fun t _ => measurable_const.indicator (hlaw i T t).1)

theorem Randomized.measurable_rangeSum (A : Randomized k Ω) (μ : Measure Ω)
    (hlaw : A.LazyLaw μ) (b T : ℕ) :
    Measurable fun ω => (rangeSum b T (A.increments ω) : ℝ≥0∞) := by
  simp only [rangeSum, Nat.cast_sum]
  exact Finset.measurable_sum _ (fun i _ => A.measurable_range μ hlaw i T)

theorem Randomized.lintegral_rangeSum (A : Randomized k Ω) (μ : Measure Ω)
    (hlaw : A.LazyLaw μ) (b T : ℕ) :
    (∫⁻ ω, (rangeSum b T (A.increments ω) : ℝ≥0∞) ∂μ) ≤
      (b : ℝ≥0∞) * ENNReal.ofReal (2 * Real.sqrt (2 * (T : ℝ))) := by
  simp only [rangeSum, Nat.cast_sum]
  rw [lintegral_finsetSum _ (fun i _ => A.measurable_range μ hlaw i T)]
  exact (Finset.sum_le_sum (fun i _ => A.lintegral_range μ hlaw i T)).trans_eq
    (by simp [nsmul_eq_mul])

end Cycle
end RandomWalkSearch
