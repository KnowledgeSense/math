import MainTheorems.Chores.NonpureExchange

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace ExchangeData

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ f : E → A} {a b : A} {q : ℕ}

theorem minimum_of_counts (B : ExchangeData M S f a b)
    (hf : EnergyMinimum M S f₀ f)
    (hcounts : expensiveCount M f a a = expensiveCount M f b b + 1) :
    EnergyMinimum M S f₀ B.allocation :=
  EnergyMinimum.of_same_energy M hf (B.feasible hf.1) (B.energy_same hcounts)

theorem no_outgoing_source_of_counts (B : ExchangeData M S f a b)
    (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hcounts : expensiveCount M f a a = expensiveCount M f b b + 1)
    {c : A} (hc : c ∈ S) : ¬Bad M B.allocation a c := by
  intro hnew
  have hla := B.source_own_expensive
  by_cases hcb : c = b
  · subst c
    have hab := B.source_sees_target
    have hge := separated_observer_expensive_ge M hf.1.1 B.source_mem (b := b)
    have hlt := hnew.2.2
    omega
  · have hca : c ≠ a := hnew.1.symm
    have hnewcounts := (minimum_bad_counts M (B.minimum_of_counts hf hcounts)
      (B.balanced hs) B.source_mem hc hnew).1
    rw [B.other_expensive c hca hcb] at hnewcounts
    obtain ⟨d, hd, hcheap⟩ := bad_target_cheap M hnew (B.balanced hs)
    rw [B.other_bundle hca hcb] at hd
    have hbound := minimum_exchange_bound M hf B.source_mem hc hnew.1 hd hcheap
    omega

theorem no_incoming_source_of_counts (B : ExchangeData M S f a b)
    (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hcounts : expensiveCount M f a a = expensiveCount M f b b + 1)
    (hn : ¬Pure M f a b) {c : A} (hc : c ∈ S) : ¬Bad M B.allocation c a := by
  intro hnew
  have hp := minimum_bad_target_pure M (B.minimum_of_counts hf hcounts) (B.balanced hs)
    hc B.source_mem hnew
  exact (pure_not_mixed M hnew.1.symm hp) (B.source_mixed hn)

theorem no_incoming_target_of_counts (B : ExchangeData M S f a b)
    (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hcounts : expensiveCount M f a a = expensiveCount M f b b + 1)
    {c : A} (hc : c ∈ S) : ¬Bad M B.allocation c b := by
  intro hnew
  have hca : c ≠ a := by
    intro h
    subst c
    exact B.no_outgoing_source_of_counts hf hs hcounts B.target_mem hnew
  have hcb : c ≠ b := hnew.1
  have hnewcounts := (minimum_bad_counts M (B.minimum_of_counts hf hcounts)
    (B.balanced hs) hc B.target_mem hnew).1
  rw [B.other_expensive c hca hcb, B.target_own_expensive] at hnewcounts
  obtain ⟨d, hd, hcheap⟩ := bad_target_cheap M hnew (B.balanced hs)
  rw [B.target_bundle] at hd
  have hold : d ∈ bundle f b := by
    rcases Finset.mem_insert.mp hd with h | h
    · subst d
      exact False.elim ((filler_not_cheap M hc B.filler) hcheap)
    · exact Finset.mem_of_mem_erase h
  have hbound := minimum_exchange_bound M hf hc B.target_mem hcb hold hcheap
  omega

theorem bad_outside_target_of_counts (B : ExchangeData M S f a b)
    (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hcounts : expensiveCount M f a a = expensiveCount M f b b + 1)
    (hn : ¬Pure M f a b) {c d : A} (hc : c ∈ S) (hd : d ∈ S) (hcb : c ≠ b)
    (hnew : Bad M B.allocation c d) : Bad M f c d := by
  have hca : c ≠ a := by
    intro h
    subst c
    exact B.no_outgoing_source_of_counts hf hs hcounts hd hnew
  have hda : d ≠ a := by
    intro h
    subst d
    exact B.no_incoming_source_of_counts hf hs hcounts hn hc hnew
  have hdb : d ≠ b := by
    intro h
    subst d
    exact B.no_incoming_target_of_counts hf hs hcounts hc hnew
  unfold Bad OwnCheap at hnew ⊢
  rw [B.other_bundle hca hcb, B.other_expensive c hda hdb,
    B.other_expensive c hca hcb] at hnew
  exact hnew

end ExchangeData

end ResearchMain.Chores
