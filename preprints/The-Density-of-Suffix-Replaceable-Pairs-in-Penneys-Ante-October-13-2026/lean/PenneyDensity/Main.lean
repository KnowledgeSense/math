import PenneyDensity.DiagonalConvention

noncomputable section
namespace PenneyDensity
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

 theorem density_le_one (n : ℕ) : density n≤1 := by
  rw [density_eq_probability,probability_card_formula]
  have hp : (Fintype.card (Fin (n+n) → Bool) : ℝ)>0 := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_one hp).mpr
  exact_mod_cast Fintype.card_subtype_le
    (fun f : Fin (n+n) → Bool => PropertyR (pairWords f false) (pairWords f true))

/-- Full suffix-replacement density theorem for the literal stopped-language
property, and both distinct-pair normalizations, through all positive lengths. -/
theorem suffix_replacement_positive_density : ∃ ρ : ℝ,
    Tendsto density atTop (𝓝 ρ) ∧
    Tendsto distinctDensity atTop (𝓝 ρ) ∧
    Tendsto distinctNormalizedDensity atTop (𝓝 ρ) ∧
    positiveLowerBound≤ρ ∧ 0<ρ ∧ ρ≤1 := by
  obtain ⟨ρ,hρ,hbound,hpos⟩ := density_has_positive_limit
  exact ⟨ρ,hρ,distinct_density_tendsto hρ,distinct_normalized_tendsto hρ,
    hbound,hpos,le_of_tendsto' hρ density_le_one⟩

end PenneyDensity
