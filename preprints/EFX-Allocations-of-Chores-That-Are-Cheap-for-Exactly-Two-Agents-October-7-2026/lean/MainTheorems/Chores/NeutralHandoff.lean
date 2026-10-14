import MainTheorems.Chores.CountExchange
import MainTheorems.Chores.DirectBuffer

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace ExchangeData

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ f : E → A} {a b k : A} {q : ℕ}

theorem neutral_nonpure (B : ExchangeData M S f a k)
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hb : b ∈ S) (hbad : Bad M f a b) (hkb : k ≠ b) : ¬Pure M f a k := by
  intro hp
  have hq := optimal_bad_source_pure M hf hs B.source_mem hb hbad
  have h := pure_unique M hbad.2.1 B.distinct hbad.1 hp hq
  exact hkb h

theorem neutral_bad_source (B : ExchangeData M S f a k)
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hb : b ∈ S) (hunique : UniqueBad M S f a b) (hkb : k ≠ b)
    (hk : expensiveCount M f k k = expensiveCount M f b b)
    {c d : A} (hc : c ∈ S) (hd : d ∈ S) (hnew : Bad M B.allocation c d) : c = k := by
  have hcounts : expensiveCount M f a a = expensiveCount M f k k + 1 := by
    rw [hk]
    exact (minimum_bad_counts M (hf.energyMinimum M) hs B.source_mem hb hunique.1).1
  by_contra hck
  have hold := B.bad_outside_target_of_counts (hf.energyMinimum M) hs hcounts
    (B.neutral_nonpure hf hs hb hunique.1 hkb) hc hd hck hnew
  have hca := (hunique.2 c hc d hd hold).1
  subst c
  exact B.no_outgoing_source_of_counts (hf.energyMinimum M) hs hcounts hd hnew

theorem neutral_nonpure_efx (B : ExchangeData M S f a k)
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hb : b ∈ S) (hunique : UniqueBad M S f a b) (hkb : k ≠ b)
    (hk : expensiveCount M f k k = expensiveCount M f b b)
    {r : ℝ} (hr : 2 < r) {w : A} (hw : w ∈ S) (hbad : Bad M B.allocation k w)
    (hnp : ¬Pure M B.allocation k w) : ∃ g : E → A, EFX M r g := by
  have hcounts : expensiveCount M f a a = expensiveCount M f k k + 1 := by
    rw [hk]
    exact (minimum_bad_counts M (hf.energyMinimum M) hs B.source_mem hb hunique.1).1
  obtain ⟨g, hg, _, hsub, hstop⟩ := nonpure_walk M
    (B.minimum_of_counts (hf.energyMinimum M) hcounts) (B.balanced hs)
    B.target_mem hw hbad hnp
  have hsg : ∀ c, q ≤ (bundle g c).card ∧ (bundle g c).card ≤ q + 1 := by
    intro c
    have hcard : (bundle g c).card = (bundle f c).card :=
      (hg.1.2.1 c).trans (hf.1.2.1 c).symm
    simpa only [hcard] using hs c
  refine ⟨g, separated_minimum_efx M hr hg hsg ?_⟩
  intro c hc d hd hnew
  have hck := B.neutral_bad_source hf hs hb hunique hkb hk hc hd (hsub c hc d hd hnew)
  subst c
  exact hstop d hd hnew

theorem neutral_outgoing_pure (B : ExchangeData M S f a k)
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hb : b ∈ S) (hunique : UniqueBad M S f a b) (hkb : k ≠ b)
    (hk : expensiveCount M f k k = expensiveCount M f b b)
    {w : A} (hw : w ∈ S) (hbad : Bad M B.allocation k w) : Pure M B.allocation k w := by
  have hcounts : expensiveCount M f a a = expensiveCount M f k k + 1 := by
    rw [hk]
    exact (minimum_bad_counts M (hf.energyMinimum M) hs B.source_mem hb hunique.1).1
  by_contra hnp
  obtain ⟨g, hg, hge, hsub, hstop⟩ := nonpure_walk M
    (B.minimum_of_counts (hf.energyMinimum M) hcounts) (B.balanced hs)
    B.target_mem hw hbad hnp
  have hz : badCount M S g = 0 := by
    rw [badCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp hnew
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    have hpk := B.neutral_bad_source hf hs hb hunique hkb hk hp₁ hp₂
      (hsub p.1 hp₁ p.2 hp₂ hnew)
    have hnew' : Bad M g k p.2 := by simpa only [hpk] using hnew
    exact hstop p.2 hp₂ hnew'
  have hle := hf.2.2 g hg.1 (hge.trans (B.energy_same hcounts))
  rw [hunique.count M B.source_mem hb, hz] at hle
  omega

theorem neutral_pure_pair (B : ExchangeData M S f a k)
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hb : b ∈ S) (hunique : UniqueBad M S f a b) (hkb : k ≠ b)
    (hk : expensiveCount M f k k = expensiveCount M f b b)
    {w : A} (hw : w ∈ S) (hbad : Bad M B.allocation k w) :
    UniqueBad M S B.allocation k w ∧ Optimal M S f₀ B.allocation ∧ w ≠ a ∧ w ≠ b := by
  have hcounts : expensiveCount M f a a = expensiveCount M f k k + 1 := by
    rw [hk]
    exact (minimum_bad_counts M (hf.energyMinimum M) hs B.source_mem hb hunique.1).1
  have hmin := B.minimum_of_counts (hf.energyMinimum M) hcounts
  have hp := B.neutral_outgoing_pure hf hs hb hunique hkb hk hw hbad
  have hnewunique : UniqueBad M S B.allocation k w := by
    refine ⟨hbad, ?_⟩
    intro c hc d hd hnew
    have hck := B.neutral_bad_source hf hs hb hunique hkb hk hc hd hnew
    subst c
    exact ⟨rfl, (pure_unique M hbad.2.1 hbad.1 hnew.1 hp
      (B.neutral_outgoing_pure hf hs hb hunique hkb hk hd hnew)).symm⟩
  have hopt : Optimal M S f₀ B.allocation :=
    Optimal.of_badCount_le M hf (B.feasible hf.1) (B.energy_same hcounts)
      (by rw [hnewunique.count M B.target_mem hw, hunique.count M B.source_mem hb])
  have hwa : w ≠ a := by
    intro h
    subst w
    exact B.no_incoming_source_of_counts (hf.energyMinimum M) hs hcounts
      (B.neutral_nonpure hf hs hb hunique.1 hkb) B.target_mem hbad
  have hwb : w ≠ b := by
    intro h
    subst w
    have hpB := minimum_bad_target_pure M (hf.energyMinimum M) hs B.source_mem hb hunique.1
    have hnewB : Pure M B.allocation b a := by
      simpa only [Pure, B.other_bundle hunique.1.1.symm hkb.symm] using hpB
    have hpBK := minimum_bad_target_pure M hmin (B.balanced hs) B.target_mem hb hbad
    have hownB := bad_target_ownCheap M hmin.1.1 (B.balanced hs) B.target_mem hbad
    have h := pure_unique M hownB hunique.1.1.symm hkb.symm hnewB hpBK
    exact B.distinct h
  exact ⟨hnewunique, hopt, hwa, hwb⟩

end ExchangeData

end ResearchMain.Chores
