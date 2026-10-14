import HardCoreActivityThreshold.HeatBathVariance

/-! Variance inequalities for the explicitly constructed heat-bath chain. -/
namespace HardCoreActivityThreshold
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Approximate tensorization for the actual single-site conditional variances. -/
def VarianceTensorization (μ : FiniteLaw (Finset V)) (C : ℝ) : Prop :=
  ∀ f : Finset V → ℝ, μ.variance f ≤ C * ∑ v, siteConditionalVariance μ v f

/-- A Poincaré inequality bounds the variational gap, including singleton support. -/
theorem le_heatBathGap_of_poincare (μ : FiniteLaw (Finset V)) {c : ℝ}
    (hc : c ≤ 1) (h : ∀ f : Finset V → ℝ, c * μ.variance f ≤ dirichletForm μ f) :
    c ≤ heatBathGap μ := by
  unfold heatBathGap
  split_ifs with hex
  · apply le_csInf
    · obtain ⟨f, hf⟩ := hex
      exact ⟨_, f, hf, rfl⟩
    · rintro r ⟨f, hf, rfl⟩
      exact (le_div_iff₀ hf).mpr (h f)
  · exact hc

theorem heatBathGap_mul_variance_le_dirichletForm (μ : FiniteLaw (Finset V))
    (f : Finset V → ℝ) : heatBathGap μ * μ.variance f ≤ dirichletForm μ f := by
  by_cases hf : 0 < μ.variance f
  · exact (le_div_iff₀ hf).mp (heatBathGap_le_rayleigh μ f hf)
  · have hz : μ.variance f = 0 := le_antisymm (le_of_not_gt hf) (μ.variance_nonneg f)
    rw [hz, mul_zero]
    exact dirichletForm_nonneg μ f

/-- A size-independent tensorization constant gives a genuine `1/n` gap bound. -/
theorem VarianceTensorization.heatBathGap_lower [Nonempty V]
    {μ : FiniteLaw (Finset V)} {C : ℝ} (hC : 1 ≤ C) (h : VarianceTensorization μ C) :
    1 / (C * Fintype.card V) ≤ heatBathGap μ := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hn : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hnpos : (0 : ℝ) < Fintype.card V := lt_of_lt_of_le zero_lt_one hn
  have hprod : 1 ≤ C * Fintype.card V := by nlinarith
  apply le_heatBathGap_of_poincare μ ((div_le_one (mul_pos hCpos hnpos)).mpr hprod)
  intro f
  rw [dirichletForm_eq_mean_conditionalVariance]
  apply (le_div_iff₀ hnpos).mpr
  have hscale := mul_le_mul_of_nonneg_left (h f) (inv_nonneg.mpr hCpos.le)
  field_simp at hscale ⊢
  nlinarith

/-- Conversely, a positive gap gives variance tensorization with the correct number of sites. -/
theorem varianceTensorization_of_gap [Nonempty V]
    (μ : FiniteLaw (Finset V)) {c : ℝ} (hc : 0 < c)
    (hgap : c / Fintype.card V ≤ heatBathGap μ) : VarianceTensorization μ (1 / c) := by
  intro f
  have h := (mul_le_mul_of_nonneg_right hgap (μ.variance_nonneg f)).trans
    (heatBathGap_mul_variance_le_dirichletForm μ f)
  rw [dirichletForm_eq_mean_conditionalVariance] at h
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hh := (div_le_div_iff_of_pos_right hn).mp
    (show (c * μ.variance f) / Fintype.card V ≤
      (∑ v, siteConditionalVariance μ v f) / Fintype.card V by
        simpa only [div_mul_eq_mul_div] using h)
  rw [one_div, inv_mul_eq_div]
  exact (le_div_iff₀ hc).mpr (by nlinarith)

end HardCoreActivityThreshold
