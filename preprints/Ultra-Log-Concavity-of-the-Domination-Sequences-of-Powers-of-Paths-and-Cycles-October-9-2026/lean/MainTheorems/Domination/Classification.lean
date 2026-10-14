import MainTheorems.Domination.PathLogConcavity
import MainTheorems.Domination.CycleLogConcavity
import MainTheorems.Domination.CycleConventions

namespace ResearchMain.Domination

theorem domination_sequences_ultraLogConcave (n ℓ : ℕ) :
    UltraLogConcave (pathPower n ℓ) ∧ UltraLogConcave (cyclePower n ℓ) :=
  ⟨pathPower_ultraLogConcave n ℓ, cyclePower_ultraLogConcave n ℓ⟩

end ResearchMain.Domination
