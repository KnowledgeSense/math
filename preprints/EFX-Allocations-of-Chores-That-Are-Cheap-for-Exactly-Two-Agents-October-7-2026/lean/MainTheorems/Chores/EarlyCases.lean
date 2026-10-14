import MainTheorems.Chores.DirectBuffer

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

theorem efx_at_most_three_agents (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    (hn : 2 ≤ Fintype.card A) (hnmax : Fintype.card A ≤ 3) :
    ∃ f : E → A, EFX M r f := by
  let μ : ℝ := (Fintype.card E : ℝ) / Fintype.card A
  have hnpos : 0 < Fintype.card A := by omega
  have hμ0 : 0 ≤ μ := by dsimp [μ]; positivity
  have hμ : μ * Fintype.card A = Fintype.card E := average_balance hnpos
  by_cases hNo : ∀ U : Finset A, deficiency M μ U ≤ 0
  · exact no_deficiency_efx M hr hμ0 hμ hnpos hNo
  · have hpos : ∃ U : Finset A, 0 < deficiency M μ U := by
      push Not at hNo
      exact hNo
    obtain ⟨S, f₀, f, _, _, hH, hf, hs⟩ := initial_optimal M hμ0 hμ hnpos hpos
    have hsmall : S.card ≤ 1 := by
      have hcard := Finset.card_compl_add_card S
      omega
    refine ⟨f, separated_minimum_efx M hr (hf.energyMinimum M) hs ?_⟩
    intro a ha b hb hbad
    have hsub : {a, b} ⊆ S := by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact ha
      · exact hb
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hbad.1] at hc
    omega

end ResearchMain.Chores
