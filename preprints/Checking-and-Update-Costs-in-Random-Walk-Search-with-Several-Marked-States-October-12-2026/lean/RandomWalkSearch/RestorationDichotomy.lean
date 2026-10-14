import RandomWalkSearch.Restoration

namespace RandomWalkSearch.Cycle
open MeasureTheory
open scoped ENNReal
variable {k : ℕ} [NeZero (N k)] {Ω : Type*} [MeasurableSpace Ω]

/-- The explicit either-checks-or-updates consequence in the first main theorem. -/
theorem Randomized.restoration_dichotomy (A : Randomized k Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hobs : A.Observable)
    (b : ℕ) (hb : 1 ≤ b) (hk : 16 * (b + 1) ≤ k)
    (hA : A.Restoration b) (hs : ∀a, (1:ℝ≥0∞)/2 ≤ A.success μ a) :
    (L k : ℝ≥0∞)/128 ≤ A.averageChecks μ ∨ (N k : ℝ≥0∞)/128 ≤ A.averageUpdates μ := by
  have hkpos : 0<k := by omega
  have hL : (L k:ℝ≥0∞)≠0 := by exact_mod_cast (L_pos hkpos).ne'
  have hN : (N k:ℝ≥0∞)≠0 := by exact_mod_cast (N_pos hkpos).ne'
  by_cases hc : (L k:ℝ≥0∞)/128 ≤ A.averageChecks μ
  · exact Or.inl hc
  by_cases ha : (N k:ℝ≥0∞)/128 ≤ A.averageUpdates μ
  · exact Or.inr ha
  have hclt : A.averageChecks μ/(L k:ℝ≥0∞) < 1/128 := by
    apply (ENNReal.div_lt_iff (Or.inl hL) (Or.inl (ENNReal.natCast_ne_top _))).mpr
    simpa [div_eq_mul_inv,mul_comm] using lt_of_not_ge hc
  have halt : A.averageUpdates μ/(N k:ℝ≥0∞) < 1/128 := by
    apply (ENNReal.div_lt_iff (Or.inl hN) (Or.inl (ENNReal.natCast_ne_top _))).mpr
    simpa [div_eq_mul_inv,mul_comm] using lt_of_not_ge ha
  have hh := ENNReal.add_lt_add hclt halt
  have heq : (1:ℝ≥0∞)/128+1/128=1/64 := by
    have hr : (1:NNReal)/128+1/128=1/64 := by norm_num
    have h := congrArg (fun x:NNReal => (x:ℝ≥0∞)) hr
    simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (128:NNReal)≠0),
      ENNReal.coe_div (by norm_num : (64:NNReal)≠0), ENNReal.coe_one, ENNReal.coe_ofNat] using h
  rw [heq] at hh
  exact False.elim ((not_lt_of_ge (A.restoration_lower_bound μ hobs b hb hk hA hs)) hh)

end RandomWalkSearch.Cycle
