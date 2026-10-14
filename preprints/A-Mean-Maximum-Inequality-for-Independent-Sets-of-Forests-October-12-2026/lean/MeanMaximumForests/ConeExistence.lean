import MeanMaximumForests.ReleaseCones
import MeanMaximumForests.GeneratorMetadata
import Mathlib.Data.Set.Card

namespace MeanMaximumForests

/-- Casting all four integer coordinates to real coordinates is injective. -/
theorem IntegerVector.toReal_injective : Function.Injective IntegerVector.toReal := by
  intro v w h
  apply IntegerVector.ext
  · have he := congrArg ConeVector.p h
    change (v.p : ℝ) = w.p at he
    exact_mod_cast he
  · have he := congrArg ConeVector.q h
    change (v.q : ℝ) = w.q at he
    exact_mod_cast he
  · have he := congrArg ConeVector.x h
    change (v.x : ℝ) = w.x at he
    exact_mod_cast he
  · have he := congrArg ConeVector.y h
    change (v.y : ℝ) = w.y at he
    exact_mod_cast he

namespace Release

theorem generators0_card : (releaseGenerators false).ncard = 32 := by
  change (Set.range (fun i => (generators0 i).toReal)).ncard = 32
  simpa [Function.comp_def] using
    Set.ncard_range_of_injective (IntegerVector.toReal_injective.comp generators0_injective)

theorem generators1_card : (releaseGenerators true).ncard = 331 := by
  change (Set.range (fun i => (generators1 i).toReal)).ncard = 331
  simpa [Function.comp_def] using
    Set.ncard_range_of_injective (IntegerVector.toReal_injective.comp generators1_injective)

/-- The complete invariant-cone existence assertion, including the release's
exact generator counts, primitive integer coordinates and 87-bit bound. -/
theorem invariant_cones_exist :
    ∃ (g₀ : Fin 32 → IntegerVector) (g₁ : Fin 331 → IntegerVector)
      (C : Bool → Set ConeVector),
      Function.Injective g₀ ∧ Function.Injective g₁ ∧
      (∀ i, (g₀ i).Primitive ∧ (g₀ i).CoordinatesBelow 87) ∧
      (∀ i, (g₁ i).Primitive ∧ (g₁ i).CoordinatesBelow 87) ∧
      (generatorSet g₀).ncard = 32 ∧ (generatorSet g₁).ncard = 331 ∧
      (∀ f, C f = {v | GeneratedCone (if f then generatorSet g₁ else generatorSet g₀) v}) ∧
      InvariantConditions (47 / 100) C := by
  exact ⟨generators0, generators1, releaseCone, generators0_injective, generators1_injective,
    fun i => ⟨generators0_primitive i, generators0_bits i⟩,
    fun i => ⟨generators1_primitive i, generators1_bits i⟩,
    generators0_card, generators1_card, fun _ => rfl, release_invariant⟩

end Release
end MeanMaximumForests
