import MeanMaximumForests.PeakAnalysis.MixtureMass
import MeanMaximumForests.PeakAnalysis.FiniteConcentration

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable

 theorem eventMass_eq_indicator_decidable {Ω : Type*} [Fintype Ω] (w : FiniteLaw Ω)
    (E : Ω → Prop) [DecidablePred E] :
    w.eventMass E = w.expectation (fun x => if E x then 1 else 0) := by
  unfold FiniteLaw.eventMass FiniteLaw.expectation
  apply sum_congr rfl
  intro x _
  by_cases hx : E x <;> simp [hx]

 theorem finiteLaw_event_inter_sub {Ω : Type*} [Fintype Ω] (w : FiniteLaw Ω) (E B : Ω → Prop) :
    w.eventMass E - w.eventMass B ≤ w.eventMass (fun x => E x ∧ ¬ B x) := by
  simp only [eventMass_eq_indicator]
  rw [← FiniteLaw.expectation_sub]
  apply FiniteLaw.expectation_mono
  intro x
  by_cases he : E x <;> by_cases hb : B x <;> simp [he, hb]

/-- A quantitative lower bound for a binomial mixture at an integer within a typical conditional-mean window. -/
theorem binomial_mixture_central_lower {Ω : Type*} [Fintype Ω] (w : FiniteLaw Ω)
    (M a : Ω → ℕ) (N : ℕ) (k : ℤ) (z A r : ℝ)
    (hz : (1 / 4 : ℝ) ≤ z) (hz1 : z ≤ 1) (hA : 1 ≤ A)
    (hr : 1280 * (32 * A + 1) ≤ r) (hrN : r ^ 2 = N)
    (hMN : ∀ x, M x ≤ N)
    (htail : w.eventMass (fun x => (M x : ℝ) ≤ (N : ℝ) / 1024) ≤ 1 / 4)
    (hcentral : (1 / 2 : ℝ) ≤ w.eventMass
      (fun x => |(a x : ℝ) + (M x : ℝ) * z / (1 + z) - (k : ℝ)| ≤ A * r)) :
    Real.exp (-(120 * (32 * A) * (32 * A + 1))) ≤
      24 * r * w.expectation (fun x => binomialIntegerMass (M x) z (k - a x)) := by
  let c := Real.exp (-(120 * (32 * A) * (32 * A + 1)))
  let E := fun x => |(a x : ℝ) + (M x : ℝ) * z / (1 + z) - (k : ℝ)| ≤ A * r
  let B := fun x => (M x : ℝ) ≤ (N : ℝ) / 1024
  have hz0 : 0 < z := by linarith
  have hr0 : 0 < r := by linarith
  have hgood : (1 / 4 : ℝ) ≤ w.eventMass (fun x => E x ∧ ¬ B x) := by
    have h := finiteLaw_event_inter_sub w E B
    dsimp [E, B] at h
    linarith
  have hp (x : Ω) : c * (if E x ∧ ¬ B x then 1 else 0) ≤
      6 * r * binomialIntegerMass (M x) z (k - a x) := by
    by_cases hx : E x ∧ ¬ B x
    · rw [ite_eq_left hx, mul_one]
      let s := Real.sqrt (M x : ℝ)
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hs2 : s ^ 2 = M x := Real.sq_sqrt (Nat.cast_nonneg _)
      have hM : (N : ℝ) / 1024 < M x := lt_of_not_ge hx.2
      have hrs : r ≤ 32 * s := by nlinarith only [hM, hrN, hs2, hr0, hs0]
      have hsr : s ≤ r := by
        have hmn : (M x : ℝ) ≤ N := by exact_mod_cast hMN x
        nlinarith only [hmn, hs2, hrN, hs0, hr0]
      have hsmall : 40 * (32 * A + 1) ≤ s := by linarith
      have hindex : |((k - a x : ℤ) : ℝ) - z * M x / (1 + z)| ≤ (32 * A) * s := by
        have hnear := hx.1
        dsimp [E] at hnear
        push_cast
        rw [show (k : ℝ) - a x - z * M x / (1 + z) =
          -((a x : ℝ) + (M x : ℝ) * z / (1 + z) - k) by ring, abs_neg]
        exact hnear.trans (by nlinarith only [mul_le_mul_of_nonneg_left hrs (by linarith : 0 ≤ A)])
      have hb := binomialIntegerMass_central_lower (M x) (k - a x) z s (32 * A)
        hz hz1 (by linarith) hsmall hs2 hindex
      exact hb.trans (mul_le_mul_of_nonneg_right (by linarith : 6 * s ≤ 6 * r)
        (binomialIntegerMass_nonneg _ z hz0 _))
    · rw [ite_eq_right hx, mul_zero]
      exact mul_nonneg (by positivity) (binomialIntegerMass_nonneg _ z hz0 _)
  have he := w.expectation_mono hp
  rw [FiniteLaw.expectation_smul, ← eventMass_eq_indicator_decidable, FiniteLaw.expectation_smul] at he
  have hc := mul_le_mul_of_nonneg_left hgood (Real.exp_pos (-(120 * (32 * A) * (32 * A + 1)))).le
  change c ≤ _
  nlinarith only [he, hc]

end MeanMaximumForests.PeakAnalysis
