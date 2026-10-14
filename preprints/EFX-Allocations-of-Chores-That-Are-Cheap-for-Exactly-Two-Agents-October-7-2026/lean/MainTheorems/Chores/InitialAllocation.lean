import MainTheorems.Chores.PairStructure

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

theorem initial_optimal (M : TwoCheapModel A E) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : μ * Fintype.card A = Fintype.card E) (hn : 0 < Fintype.card A)
    (hpos : ∃ U : Finset A, 0 < deficiency M μ U) :
    ∃ S : Finset A, ∃ f₀ f : E → A,
      MaxDeficient M μ S ∧ 0 < deficiency M μ S ∧ 2 ≤ Sᶜ.card ∧
      Optimal M S f₀ f ∧ ∀ a,
        Fintype.card E / Fintype.card A ≤ (bundle f a).card ∧
        (bundle f a).card ≤ Fintype.card E / Fintype.card A + 1 := by
  obtain ⟨S, hS⟩ := exists_max_deficient M μ
  obtain ⟨U, hU⟩ := hpos
  have hp : 0 < deficiency M μ S := hU.trans_le (hS U)
  have hH := positive_deficiency_compl M hμ0 hμ hp
  obtain ⟨f₀, hf₀, hs₀⟩ := separated_balanced_allocation M hμ0 hμ hn hS
  obtain ⟨f, hf⟩ := exists_optimal M S f₀ hf₀
  refine ⟨S, f₀, f, hS, hp, hH, hf, ?_⟩
  intro a
  simpa only [hf.1.2.1 a] using hs₀ a

omit [DecidableEq A] [DecidableEq E] in
theorem average_balance (hn : 0 < Fintype.card A) :
    ((Fintype.card E : ℝ) / Fintype.card A) * Fintype.card A = Fintype.card E := by
  have hn' : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  exact div_mul_cancel₀ _ hn'

end ResearchMain.Chores
