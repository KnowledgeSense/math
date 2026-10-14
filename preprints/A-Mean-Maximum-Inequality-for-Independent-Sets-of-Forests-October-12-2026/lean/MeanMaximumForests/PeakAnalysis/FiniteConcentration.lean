import MeanMaximumForests.FiniteModeBounds

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable

 theorem eventMass_eq_indicator {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (E : Ω → Prop) :
    μ.eventMass E = μ.expectation (fun x => if E x then 1 else 0) := by
  simp only [FiniteLaw.eventMass, FiniteLaw.expectation, mul_ite, mul_one, mul_zero]

 theorem finiteLaw_central_mass_half {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (r : ℝ) (hr : 0 < r) (hvar : 2 * μ.variance X ≤ r ^ 2) :
    (1 / 2 : ℝ) ≤ μ.eventMass (fun x => |X x - μ.expectation X| ≤ r) := by
  let E := fun x => |X x - μ.expectation X| ≤ r
  have hpoint (x : Ω) : r ^ 2 * (1 - if E x then 1 else 0) ≤ (X x - μ.expectation X) ^ 2 := by
    by_cases hx : E x
    · simp only [hx, ↓reduceIte, sub_self, mul_zero]
      positivity
    · have hx' : r < |X x - μ.expectation X| := lt_of_not_ge hx
      simp only [hx, ↓reduceIte, sub_zero, mul_one]
      nlinarith only [sq_abs (X x - μ.expectation X), hr, hx']
  have h := μ.expectation_mono hpoint
  rw [FiniteLaw.expectation_smul, FiniteLaw.expectation_sub, FiniteLaw.expectation_const,
    ← eventMass_eq_indicator] at h
  change r ^ 2 * (1 - μ.eventMass E) ≤ μ.variance X at h
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  change (1 / 2 : ℝ) ≤ μ.eventMass E
  nlinarith only [h, hvar, hr2]

/-- A global mode carries at least a constant times the reciprocal concentration radius. -/
theorem finiteLaw_mode_mass_lower {N : ℕ} (μ : FiniteLaw (Fin N)) (k : Fin N)
    (hmode : ∀ j, μ.mass j ≤ μ.mass k) (r : ℝ) (hr : 1 ≤ r)
    (hvar : 2 * μ.variance (fun j => (j.val : ℝ)) ≤ r ^ 2) :
    (1 : ℝ) ≤ 6 * r * μ.mass k := by
  let S := univ.filter (fun j : Fin N => |(j.val : ℝ) - μ.expectation (fun j => (j.val : ℝ))| ≤ r)
  have hmass := finiteLaw_central_mass_half μ (fun j => (j.val : ℝ)) r (by linarith) hvar
  have hcard : (S.card : ℝ) ≤ 2 * r + 1 :=
    fin_span_card S _ r (by linarith) (fun j hj => (mem_filter.mp hj).2)
  have hmass' : (1 / 2 : ℝ) ≤ ∑ j ∈ S, μ.mass j := by
    simpa only [FiniteLaw.eventMass, S, sum_filter] using hmass
  have hsum : (∑ j ∈ S, μ.mass j) ≤ (S.card : ℝ) * μ.mass k := by
    have h := sum_le_sum (s := S) (f := μ.mass) (g := fun _ => μ.mass k) (fun j _ => hmode j)
    simpa only [sum_const, nsmul_eq_mul] using h
  have hc := mul_le_mul_of_nonneg_right hcard (μ.nonneg k)
  have hc' := mul_le_mul_of_nonneg_right (by linarith : 2 * r + 1 ≤ 3 * r) (μ.nonneg k)
  nlinarith only [hmass', hsum, hc, hc']

end MeanMaximumForests.PeakAnalysis
