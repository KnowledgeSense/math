import MainTheorems.Chores.NeutralRepair

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace ExchangeData

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ f : E → A} {a b : A} {q : ℕ}

theorem reverse_unique_pair (B : ExchangeData M S f a b)
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hunique : UniqueBad M S f a b) :
    UniqueBad M S B.allocation b a ∧ Optimal M S f₀ B.allocation ∧
      expensiveCount M B.allocation a a = expensiveCount M f b b := by
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs B.source_mem B.target_mem hunique.1).1
  have hp := optimal_bad_source_pure M hf hs B.source_mem B.target_mem hunique.1
  have hE := B.source_own_expensive
  have hEa : expensiveCount M B.allocation a a = expensiveCount M f b b := by omega
  have hown : OwnCheap M B.allocation b := by
    have htwo := optimal_bad_target_two_cheap M hf hs B.source_mem B.target_mem hunique.1
    have hcheap := B.target_cheap_count
    rw [ownCheap_iff_count]
    omega
  have hbad : Bad M B.allocation b a := by
    refine ⟨B.distinct.symm, hown, ?_⟩
    rw [pure_observer_expensive M (B.feasible hf.1).1 B.target_mem (B.source_pure hp),
      hEa, B.target_own_expensive]
    omega
  have hnewunique : UniqueBad M S B.allocation b a := by
    refine ⟨hbad, ?_⟩
    intro c hc d hd hnew
    have hcb : c = b := by
      by_contra hcb
      have hold := B.bad_outside_source_of_pure (hf.energyMinimum M) hs hunique.1 hp hc hd hcb hnew
      have hca := (hunique.2 c hc d hd hold).1
      subst c
      exact B.no_outgoing_source (hf.energyMinimum M) hs hunique.1 hd hnew
    subst c
    have hda : d = a := by
      by_contra hda
      have hdb : d ≠ b := hnew.1.symm
      have hmargin := optimal_pair_low_margin M hf hs B.source_mem B.target_mem hd hunique.1 hda hdb
      have hlt := hnew.2.2
      rw [B.target_own_expensive, B.other_expensive b hda hdb] at hlt
      omega
    exact ⟨rfl, hda⟩
  have hopt : Optimal M S f₀ B.allocation :=
    Optimal.of_badCount_le M hf (B.feasible hf.1) (B.energy_same hcounts)
      (by rw [hnewunique.count M B.target_mem B.source_mem,
        hunique.count M B.source_mem B.target_mem])
  exact ⟨hnewunique, hopt, hEa⟩

end ExchangeData

theorem neutral_handoff_either_endpoint (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b k : A} (ha : a ∈ S) (hb : b ∈ S) (hkS : k ∈ S)
    (hunique : UniqueBad M S f a b) (hka : k ≠ a) (hkb : k ≠ b)
    (hk : expensiveCount M f k k = expensiveCount M f b b)
    (hL : expensiveCount M f b b + 2 ≤ q) {d : E}
    (hd : d ∈ bundle f k) (hcheap : M.Cheap a d ∨ M.Cheap b d) :
    ∃ g : E → A, EFX M r g := by
  rcases hcheap with hcheap | hcheap
  · exact neutral_handoff M hr hf hs ha hb hkS hunique hka hkb hk hL hd hcheap
  · obtain ⟨B⟩ := exists_basic_exchange M hf.1.1 hs ha hb hunique.1
    obtain ⟨hunique', hf', hEa⟩ := B.reverse_unique_pair hf hs hunique
    have hk' : expensiveCount M B.allocation k k = expensiveCount M B.allocation a a := by
      rw [B.other_expensive k hka hkb, hEa, hk]
    have hL' : expensiveCount M B.allocation a a + 2 ≤ q := by rwa [hEa]
    have hd' : d ∈ bundle B.allocation k := by rw [B.other_bundle hka hkb]; exact hd
    exact neutral_handoff M hr hf' (B.balanced hs) hb ha hkS hunique' hkb hka hk' hL' hd' hcheap

end ResearchMain.Chores
