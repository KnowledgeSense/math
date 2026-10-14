import MeanMaximumForests.PeakAnalysis.BinomialGradient
import MeanMaximumForests.PeakAnalysis.BinomialMixtureLower

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable

 theorem finiteLaw_abs_expectation_le {Ω : Type*} [Fintype Ω] (w : FiniteLaw Ω) (f : Ω → ℝ) :
    |w.expectation f| ≤ w.expectation (fun x => |f x|) := by
  unfold FiniteLaw.expectation
  calc
    _ ≤ ∑ x, |w.mass x * f x| := abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (w.nonneg _)]

 theorem binomial_integer_adjacent_le_one (n : ℕ) (k : ℤ) (z : ℝ) (hz : 0 < z) :
    |binomialIntegerMass n z (k + 1) - binomialIntegerMass n z k| ≤ 1 := by
  rw [abs_le]
  have h0 := binomialIntegerMass_nonneg n z hz k
  have h1 := binomialIntegerMass_nonneg n z hz (k + 1)
  have h2 := binomialIntegerMass_le_one n z hz k
  have h3 := binomialIntegerMass_le_one n z hz (k + 1)
  constructor <;> linarith

 theorem binomial_mixture_gradient {Ω : Type*} [Fintype Ω] (w : FiniteLaw Ω)
    (M a : Ω → ℕ) (N : ℕ) (k : ℤ) (z B : ℝ)
    (hz : (1 / 4 : ℝ) ≤ z) (hz1 : z ≤ 1) (hN : 1024 * 28802 ≤ N)
    (htail : (N : ℝ) * w.eventMass (fun x => (M x : ℝ) ≤ (N : ℝ) / 1024) ≤ B) :
    (N : ℝ) * |w.expectation (fun x => binomialIntegerMass (M x) z (k + 1 - a x)) -
      w.expectation (fun x => binomialIntegerMass (M x) z (k - a x))| ≤
        1024 * (6 * (Real.exp 720) ^ 2) + B := by
  let D := 6 * (Real.exp 720) ^ 2
  let E := fun x => (M x : ℝ) ≤ (N : ℝ) / 1024
  let f := fun x => binomialIntegerMass (M x) z (k + 1 - a x) -
    binomialIntegerMass (M x) z (k - a x)
  have hz0 : 0 < z := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hp (x : Ω) : (N : ℝ) * |f x| ≤ 1024 * D + (N : ℝ) * (if E x then 1 else 0) := by
    have heq : k + 1 - (a x : ℤ) = (k - a x) + 1 := by omega
    by_cases hx : E x
    · simp only [hx, ↓reduceIte, mul_one]
      have h := binomial_integer_adjacent_le_one (M x) (k - a x) z hz0
      have h' : |f x| ≤ 1 := by simpa only [f, heq] using h
      have hn := mul_le_mul_of_nonneg_left h' (Nat.cast_nonneg (α := ℝ) N)
      nlinarith only [hn, hD]
    · simp only [hx, ↓reduceIte, mul_zero, add_zero]
      have hlarge : (N : ℝ) < 1024 * M x := by dsimp [E] at hx; linarith
      have hmn : 28802 ≤ M x := by
        have hn : (1024 * 28802 : ℝ) ≤ N := by exact_mod_cast hN
        have hm : (28802 : ℝ) ≤ M x := by linarith
        exact_mod_cast hm
      have h := binomial_integer_gradient_large (M x) (k - a x) z hz hz1 hmn
      have h' : (M x : ℝ) * |f x| ≤ D := by simpa only [f, heq, D] using h
      have hh := mul_le_mul_of_nonneg_right hlarge.le (abs_nonneg (f x))
      nlinarith only [hh, h']
  have he := w.expectation_mono hp
  rw [FiniteLaw.expectation_smul, FiniteLaw.expectation_add, FiniteLaw.expectation_const,
    FiniteLaw.expectation_smul, ← eventMass_eq_indicator_decidable] at he
  have hab := mul_le_mul_of_nonneg_left (finiteLaw_abs_expectation_le w f) (Nat.cast_nonneg (α := ℝ) N)
  rw [← FiniteLaw.expectation_sub]
  change (N : ℝ) * |w.expectation f| ≤ 1024 * D + B
  have ht : (N : ℝ) * w.eventMass E ≤ B := htail
  exact hab.trans (he.trans (by linarith only [ht]))

end MeanMaximumForests.PeakAnalysis
