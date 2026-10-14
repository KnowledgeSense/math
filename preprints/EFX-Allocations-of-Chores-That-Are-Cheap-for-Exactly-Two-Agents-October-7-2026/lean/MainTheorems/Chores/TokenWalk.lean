import MainTheorems.Chores.TokenWalkInitial

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace TokenWalkState

theorem terminates {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {P : TokenReady M S f₀ q k} {B : TokenSeed P} {r : ℝ} (hr : 2 < r)
    (W : TokenWalkState B r) : ∃ g : E → A, EFX M r g := by
  classical
  have h : ∀ n, ∀ V : TokenWalkState B r, P.walkAgents.card - V.passed.card = n →
      ∃ g : E → A, EFX M r g := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V hn
      by_cases hstop : ∀ w ∈ P.walkAgents, V.current ≠ w →
          expensiveCount M P.allocation V.current V.current + 1 ≤
            expensiveCount M V.allocation V.current w
      · exact ⟨V.allocation, V.terminal_efx hr hstop⟩
      · push Not at hstop
        obtain ⟨w, hw, hvw, hfail⟩ := hstop
        obtain ⟨D⟩ := V.exists_step hw hvw hfail
        have hsub : insert V.current V.passed ⊆ P.walkAgents := by
          intro u hu
          rcases Finset.mem_insert.mp hu with hu | hu
          · exact hu ▸ V.current_mem
          · exact V.passed_subset hu
        have hc := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem V.current_new] at hc
        have hdec : P.walkAgents.card - (D.advance hr).passed.card < n := by
          rw [D.advance_passed_card hr]
          omega
        exact ih _ hdec (D.advance hr) rfl
  exact h _ W rfl

end TokenWalkState

theorem token_ready_efx {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {r : ℝ} (hr : 2 < r) (P : TokenReady M S f₀ q k) : ∃ g : E → A, EFX M r g := by
  obtain ⟨B⟩ := exists_token_seed P
  exact (B.initial_state hr).terminates hr

theorem token_pair_efx (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ v, q ≤ (bundle f v).card ∧ (bundle f v).card ≤ q + 1)
    {a b k : A} (ha : a ∈ S) (hb : b ∈ S) (hkS : k ∈ S)
    (hunique : UniqueBad M S f a b) (hka : k ≠ a) (hkb : k ≠ b)
    (hL : expensiveCount M f b b + 3 ≤ q) (hkpos : 0 < expensiveCount M f k k) :
    ∃ g : E → A, EFX M r g := by
  rcases prepare_token_pair M hr hf hs ha hb hkS hunique hka hkb hL hkpos with h | h
  · exact h
  · obtain ⟨P⟩ := h
    exact token_ready_efx hr P

end ResearchMain.Chores
