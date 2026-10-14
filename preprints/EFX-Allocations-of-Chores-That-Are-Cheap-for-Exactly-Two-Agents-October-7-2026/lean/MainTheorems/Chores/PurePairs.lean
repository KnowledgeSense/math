import MainTheorems.Chores.NonpureWalk

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace ExchangeData

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ f : E → A} {a b : A} {q : ℕ}

theorem no_incoming_source_outside (B : ExchangeData M S f a b)
    (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ v, q ≤ (bundle f v).card ∧ (bundle f v).card ≤ q + 1)
    (hbad : Bad M f a b) (hp : Pure M f a b) {c : A} (hc : c ∈ S) (hcb : c ≠ b) :
    ¬Bad M B.allocation c a := by
  intro hnew
  obtain ⟨d, hd, hcheap⟩ := bad_target_cheap M hnew (B.balanced hs)
  have hown := separated_owner_cheap M (B.minimum hf hs hbad).1.1 hc hcheap
  rw [(mem_bundle B.allocation a d).mp hd] at hown
  have hbc := B.source_pure hp d hd hown
  exact (two_cheap_third M B.distinct hown hbc hnew.1 hcb) hcheap

theorem bad_outside_source_of_pure (B : ExchangeData M S f a b)
    (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ v, q ≤ (bundle f v).card ∧ (bundle f v).card ≤ q + 1)
    (hbad : Bad M f a b) (hp : Pure M f a b) {c d : A}
    (hc : c ∈ S) (hd : d ∈ S) (hcb : c ≠ b) (hnew : Bad M B.allocation c d) :
    Bad M f c d := by
  have hca : c ≠ a := by
    intro h
    subst c
    exact B.no_outgoing_source hf hs hbad hd hnew
  have hda : d ≠ a := by
    intro h
    subst d
    exact B.no_incoming_source_outside hf hs hbad hp hc hcb hnew
  have hdb : d ≠ b := by
    intro h
    subst d
    exact B.no_incoming_target hf hs hbad hc hnew
  unfold Bad OwnCheap at hnew ⊢
  rw [B.other_bundle hca hcb, B.other_expensive c hda hdb,
    B.other_expensive c hca hcb] at hnew
  exact hnew

end ExchangeData

omit [DecidableEq E] in
theorem bad_target_ownCheap (M : TwoCheapModel A E) {S : Finset A} {f : E → A} {q : ℕ}
    (hf : Separated M S f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hbad : Bad M f a b) : OwnCheap M f b := by
  obtain ⟨d, hd, hcheap⟩ := bad_target_cheap M hbad hs
  have h := separated_owner_cheap M hf ha hcheap
  rw [(mem_bundle f b d).mp hd] at h
  exact ⟨d, hd, h⟩

theorem optimal_bad_target_two_cheap (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) :
    2 ≤ cheapCount M f b b := by
  have hown := bad_target_ownCheap M hf.1.1 hs ha hbad
  have hpos := (ownCheap_iff_count M f b).mp hown
  by_contra hlt
  have hone : cheapCount M f b b = 1 := by omega
  have hp := optimal_bad_source_pure M hf hs ha hb hbad
  obtain ⟨B⟩ := exists_basic_exchange M hf.1.1 hs ha hb hbad
  have hnewcount := B.target_cheap_count
  have hzero : cheapCount M B.allocation b b = 0 := by omega
  have hnewown : ¬OwnCheap M B.allocation b := by
    rw [ownCheap_iff_count, hzero]
    exact Nat.lt_irrefl 0
  have hsub : BadSubset M S B.allocation f := by
    intro c hc d hd hnew
    have hcb : c ≠ b := by
      intro heq
      subst c
      exact hnewown hnew.2.1
    exact B.bad_outside_source_of_pure (hf.energyMinimum M) hs hbad hp hc hd hcb hnew
  have henergy := B.energy_same
    (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hbad).1
  have hstrict := badCount_strict M hsub ha hb hbad
    (B.no_outgoing_source (hf.energyMinimum M) hs hbad hb)
  have hmin := hf.2.2 B.allocation (B.feasible hf.1) henergy
  omega

theorem optimal_pair_no_other_outgoing (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b c : A} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hbad : Bad M f a b)
    (hcb : c ≠ b) : ¬Bad M f a c := by
  intro hnew
  have hp := optimal_bad_source_pure M hf hs ha hb hbad
  have hq := optimal_bad_source_pure M hf hs ha hc hnew
  have heq := pure_unique M hbad.2.1 hbad.1 hnew.1 hp hq
  exact hcb heq.symm

theorem optimal_pair_high_margin (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b c : A} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hbad : Bad M f a b)
    (hca : c ≠ a) (hcb : c ≠ b) :
    expensiveCount M f b b + 1 ≤ expensiveCount M f a c := by
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hbad).1
  have hn := optimal_pair_no_other_outgoing M hf hs ha hb hc hbad hcb
  by_contra h
  have hlt : expensiveCount M f a c < expensiveCount M f a a := by omega
  exact hn ⟨hca.symm, hbad.2.1, hlt⟩

theorem optimal_pair_low_margin (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b c : A} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hbad : Bad M f a b)
    (hca : c ≠ a) (hcb : c ≠ b) :
    expensiveCount M f b b + 1 ≤ expensiveCount M f b c := by
  by_contra hmargin
  have hle : expensiveCount M f b c ≤ expensiveCount M f b b := by omega
  have hp := optimal_bad_source_pure M hf hs ha hb hbad
  have hpt := minimum_bad_target_pure M (hf.energyMinimum M) hs ha hb hbad
  have htwo := optimal_bad_target_two_cheap M hf hs ha hb hbad
  obtain ⟨B⟩ := exists_basic_exchange M hf.1.1 hs ha hb hbad
  have henergy := B.energy_same
    (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hbad).1
  have hnewmin := B.minimum (hf.energyMinimum M) hs hbad
  have hnewcheap := B.target_cheap_count
  have hnewown : OwnCheap M B.allocation b := by
    rw [ownCheap_iff_count]
    omega
  have hnewbc : Bad M B.allocation b c := by
    refine ⟨hcb.symm, hnewown, ?_⟩
    rw [B.other_expensive b hca hcb, B.target_own_expensive]
    omega
  have hnp : ¬Pure M B.allocation b c := by
    intro hpnew
    have heq := pure_unique M hnewown hbad.1.symm hcb.symm (B.target_pure hpt) hpnew
    exact hca heq.symm
  obtain ⟨g, hg, hge, hsub, hstop⟩ := nonpure_walk M hnewmin (B.balanced hs) hb hc hnewbc hnp
  have hsubold : BadSubset M S g f := by
    intro v hv w hw hvw
    have hvb : v ≠ b := by
      intro heq
      subst v
      exact hstop w hw hvw
    exact B.bad_outside_source_of_pure (hf.energyMinimum M) hs hbad hp hv hw hvb
      (hsub v hv w hw hvw)
  have hnotab : ¬Bad M g a b := by
    intro hnew
    exact B.no_outgoing_source (hf.energyMinimum M) hs hbad hb (hsub a ha b hb hnew)
  have hstrict := badCount_strict M hsubold ha hb hbad hnotab
  have hmin := hf.2.2 g hg.1 (hge.trans henergy)
  omega

end ResearchMain.Chores
