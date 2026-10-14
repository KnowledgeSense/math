import MainTheorems.Chores.BasicExchange

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

def nonMixedCount (M : TwoCheapModel A E) (S : Finset A) (f : E → A) : ℕ :=
  (S.filter (fun a => ¬Mixed M f a)).card

namespace ExchangeData

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ f : E → A} {a b : A} {q : ℕ}

theorem balanced (B : ExchangeData M S f a b)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) :
    ∀ c, q ≤ (bundle B.allocation c).card ∧ (bundle B.allocation c).card ≤ q + 1 := by
  intro c
  simpa only [B.card] using hs c

theorem minimum (B : ExchangeData M S f a b) (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) (hbad : Bad M f a b) :
    EnergyMinimum M S f₀ B.allocation :=
  EnergyMinimum.of_same_energy M hf (B.feasible hf.1)
    (B.energy_same (minimum_bad_counts M hf hs B.source_mem B.target_mem hbad).1)

theorem no_outgoing_source (B : ExchangeData M S f a b) (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) (hbad : Bad M f a b)
    {c : A} (hc : c ∈ S) : ¬Bad M B.allocation a c := by
  intro hnew
  have hcounts := minimum_bad_counts M hf hs B.source_mem B.target_mem hbad
  have hla := B.source_own_expensive
  by_cases hcb : c = b
  · subst c
    have hab := B.source_sees_target
    have hlt := hnew.2.2
    omega
  · have hca : c ≠ a := hnew.1.symm
    have hnewmin := B.minimum hf hs hbad
    have hnewcounts := (minimum_bad_counts M hnewmin (B.balanced hs) B.source_mem hc hnew).1
    rw [B.other_expensive c hca hcb] at hnewcounts
    obtain ⟨d, hd, hcheap⟩ := bad_target_cheap M hnew (B.balanced hs)
    rw [B.other_bundle hca hcb] at hd
    have hbound := minimum_exchange_bound M hf B.source_mem hc hnew.1 hd hcheap
    omega

theorem no_incoming_source (B : ExchangeData M S f a b) (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) (hbad : Bad M f a b)
    (hn : ¬Pure M f a b) {c : A} (hc : c ∈ S) : ¬Bad M B.allocation c a := by
  intro hnew
  have hp := minimum_bad_target_pure M (B.minimum hf hs hbad) (B.balanced hs)
    hc B.source_mem hnew
  exact (pure_not_mixed M hnew.1.symm hp) (B.source_mixed hn)

theorem no_incoming_target (B : ExchangeData M S f a b) (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) (hbad : Bad M f a b)
    {c : A} (hc : c ∈ S) : ¬Bad M B.allocation c b := by
  intro hnew
  have hp := B.target_pure (minimum_bad_target_pure M hf hs B.source_mem B.target_mem hbad)
  have hca : c ≠ a := by
    intro h
    subst c
    exact B.no_outgoing_source hf hs hbad B.target_mem hnew
  obtain ⟨d, hd, hcheap⟩ := bad_target_cheap M hnew (B.balanced hs)
  have hown := separated_owner_cheap M (B.minimum hf hs hbad).1.1 hc hcheap
  rw [(mem_bundle B.allocation b d).mp hd] at hown
  have hac := hp d hd hown
  exact (two_cheap_third M B.distinct hac hown hca hnew.1) hcheap

theorem target_nonpure (B : ExchangeData M S f a b) (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) (hbad : Bad M f a b)
    (hn : ¬Pure M f a b) {c : A} (hc : c ∈ S) (hnew : Bad M B.allocation b c) :
    ¬Pure M B.allocation b c := by
  intro hpnew
  have hp := B.target_pure (minimum_bad_target_pure M hf hs B.source_mem B.target_mem hbad)
  have hca : c ≠ a := by
    intro h
    subst c
    exact B.no_incoming_source hf hs hbad hn B.target_mem hnew
  obtain ⟨d, hd, hown⟩ := hnew.2.1
  have hac := hp d hd hown
  exact (two_cheap_third M B.distinct hac hown hca hnew.1.symm) (hpnew d hd hown)

theorem target_not_mixed (B : ExchangeData M S f a b) (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) (hbad : Bad M f a b) :
    ¬Mixed M B.allocation b :=
  pure_not_mixed M B.distinct.symm
    (B.target_pure (minimum_bad_target_pure M hf hs B.source_mem B.target_mem hbad))

theorem bad_outside_target (B : ExchangeData M S f a b) (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) (hbad : Bad M f a b)
    (hn : ¬Pure M f a b) {c d : A} (hc : c ∈ S) (hd : d ∈ S) (hcb : c ≠ b)
    (hnew : Bad M B.allocation c d) : Bad M f c d := by
  have hca : c ≠ a := by
    intro h
    subst c
    exact B.no_outgoing_source hf hs hbad hd hnew
  have hda : d ≠ a := by
    intro h
    subst d
    exact B.no_incoming_source hf hs hbad hn hc hnew
  have hdb : d ≠ b := by
    intro h
    subst d
    exact B.no_incoming_target hf hs hbad hc hnew
  unfold Bad OwnCheap at hnew ⊢
  rw [B.other_bundle hca hcb, B.other_expensive c hda hdb,
    B.other_expensive c hca hcb] at hnew
  exact hnew

theorem mixed_preserved (B : ExchangeData M S f a b) (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) (hbad : Bad M f a b)
    (hn : ¬Pure M f a b) {c : A} (hm : Mixed M f c) : Mixed M B.allocation c := by
  by_cases hca : c = a
  · subst c
    exact B.source_mixed hn
  · by_cases hcb : c = b
    · subst c
      exact False.elim ((pure_not_mixed M B.distinct.symm
        (minimum_bad_target_pure M hf hs B.source_mem B.target_mem hbad)) hm)
    · simpa only [Mixed, B.other_bundle hca hcb] using hm

theorem nonMixed_decreases (B : ExchangeData M S f a b) (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) (hbad : Bad M f a b)
    (hn : ¬Pure M f a b) (hm : ¬Mixed M f a) :
    nonMixedCount M S B.allocation < nonMixedCount M S f := by
  have hsub : insert a (S.filter (Mixed M f)) ⊆ S.filter (Mixed M B.allocation) := by
    intro c hc
    rcases Finset.mem_insert.mp hc with h | h
    · subst c
      exact Finset.mem_filter.mpr ⟨B.source_mem, B.source_mixed hn⟩
    · have h' := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨h'.1, B.mixed_preserved hf hs hbad hn h'.2⟩
  have ha : a ∉ S.filter (Mixed M f) := by simp [hm]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem ha] at hc
  have hold := Finset.card_filter_add_card_filter_not (s := S) (Mixed M f)
  have hnew := Finset.card_filter_add_card_filter_not (s := S) (Mixed M B.allocation)
  unfold nonMixedCount
  omega

end ExchangeData

end ResearchMain.Chores
