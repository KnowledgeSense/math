import HardCoreActivityThreshold.FiniteSiteFormula

/-! Marginalizing one Boolean coordinate without changing the ambient vertex type. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def erasedLaw (μ : FiniteLaw (Finset V)) (v : V) : FiniteLaw (Finset V) where
  mass s := if v ∉ s then μ.mass s + μ.mass (insert v s) else 0
  nonneg s := by
    by_cases hs : v ∈ s
    · simp [hs]
    · simpa [hs] using add_nonneg (μ.nonneg s) (μ.nonneg (insert v s))
  sum_one := by rw [← sum_config_split, μ.sum_one]

theorem erasedLaw_expectation (μ : FiniteLaw (Finset V)) (v : V) (f : Finset V → ℝ) :
    (erasedLaw μ v).expectation f = μ.expectation (fun s => f (s.erase v)) := by
  unfold FiniteLaw.expectation
  rw [sum_config_split v (fun s => μ.mass s * f (s.erase v))]
  apply sum_congr rfl
  intro s _
  by_cases hs : v ∉ s <;> simp [erasedLaw, hs, erase_eq_of_notMem, add_mul]

theorem erasedLaw_variance (μ : FiniteLaw (Finset V)) (v : V) (f : Finset V → ℝ) :
    (erasedLaw μ v).variance f = μ.variance (fun s => f (s.erase v)) := by
  rw [FiniteLaw.variance_eq_second_moment, FiniteLaw.variance_eq_second_moment,
    erasedLaw_expectation, erasedLaw_expectation]

omit [DecidableEq V] in
theorem FiniteLaw.variance_congr_on_support (μ : FiniteLaw (Finset V))
    {f g : Finset V → ℝ} (h : ∀ s, 0 < μ.mass s → f s = g s) :
    μ.variance f = μ.variance g := by
  rw [μ.variance_eq_second_moment, μ.variance_eq_second_moment,
    μ.expectation_congr_on_support h,
    μ.expectation_congr_on_support (fun s hs => congrArg (fun x : ℝ => x^2) (h s hs))]

theorem erasedLaw_siteOperator_variance (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) :
    (erasedLaw μ v).variance (siteOperator μ v f) = μ.variance (siteOperator μ v f) := by
  rw [erasedLaw_variance]
  apply μ.variance_congr_on_support
  intro s hs
  exact (siteOperator_sameOutside μ v f (by simp [sameOutside] : sameOutside v s (s.erase v))
    (fiberMass_pos_of_mass_pos μ v hs).ne').symm

/-- Total variance, with the marginal law explicitly normalized on erased configurations. -/
theorem variance_erase_decomposition (μ : FiniteLaw (Finset V)) (v : V)
    (f : Finset V → ℝ) :
    μ.variance f = siteConditionalVariance μ v f +
      (erasedLaw μ v).variance (siteOperator μ v f) := by
  rw [erasedLaw_siteOperator_variance, siteConditionalVariance_eq_variance_sub]
  ring

end HardCoreActivityThreshold
