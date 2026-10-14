import MainTheorems.Chores.PairReduction
import MainTheorems.Chores.SinglePairReduction
import MainTheorems.Chores.TokenWalk

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

theorem exists_efx (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    (hn : 2 ≤ Fintype.card A) : ∃ f : E → A, EFX M r f := by
  classical
  have hnpos : 0 < Fintype.card A := by omega
  let μ : ℝ := (Fintype.card E : ℝ) / Fintype.card A
  have hμ0 : 0 ≤ μ := by dsimp [μ]; positivity
  have hμ : μ * Fintype.card A = Fintype.card E := average_balance hnpos
  by_cases hNo : ∀ U : Finset A, deficiency M μ U ≤ 0
  · exact no_deficiency_efx M hr hμ0 hμ hnpos hNo
  · have hpos : ∃ U : Finset A, 0 < deficiency M μ U := by
      push Not at hNo
      exact hNo
    obtain ⟨S, f₀, f, hmax, _, hH, hf, hs⟩ := initial_optimal M hμ0 hμ hnpos hpos
    rcases reduce_to_unique_ordinary M hr hf hs with hefx | hpair
    · exact hefx
    · obtain ⟨a, b, ha, hb, hunique, hL⟩ := hpair
      rcases unique_ordinary_reduction M hr hf hs ha hb hunique hL hmax hμ hH with hefx | hdonor
      · exact hefx
      · obtain ⟨k, hk, hka, hkb, hkpos, hbound⟩ := hdonor
        exact token_pair_efx M hr hf hs ha hb hk hunique hka hkb hbound hkpos

end ResearchMain.Chores
