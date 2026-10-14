import MainTheorems.Chores.IsolatedSwap
import MainTheorems.Chores.RepairStats

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace IsolatedSwap

variable {M : TwoCheapModel A E} {S : Finset A} {f : E → A} {a b k : A}

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem second_pair_cheap (B : IsolatedSwap M S f a b k) {v : A} (hv : v = a ∨ v = b) :
    M.Cheap v B.secondChore := by
  rcases hv with hv | hv <;> subst v
  · exact B.highCheap
  · exact B.lowCheap

theorem other_expensive (B : IsolatedSwap M S f a b k) (v : A) {c : A}
    (hck : c ≠ k) (hcb : c ≠ b) : expensiveCount M B.allocation v c = expensiveCount M f v c := by
  rw [expensiveCount, B.other_bundle hck hcb]
  rfl

theorem pair_to_low_count (B : IsolatedSwap M S f a b k) {v : A} (hv : v = a ∨ v = b) :
    expensiveCount M B.allocation v b = expensiveCount M f v b + 1 := by
  have ht := exchange_expensive_right M f B.chore_distinct B.owner_distinct v
  rw [B.secondOwner, ite_eq_left (B.second_pair_cheap hv), ite_eq_right (B.first_pair_expensive hv)] at ht
  change (expensiveCount M B.allocation v b : ℤ) = expensiveCount M f v b - 0 + 1 at ht
  omega

theorem pair_stats (B : IsolatedSwap M S f a b k) {f₀ : E → A} {q : ℕ}
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) : OrdinaryStats M f B.allocation a b := by
  have hcounts := minimum_bad_counts M (hf.energyMinimum M) hs ha hb hbad
  have hownE {v : A} (hv : v = a ∨ v = b) :
      expensiveCount M B.allocation v v = expensiveCount M f b b + 1 := by
    rcases hv with hv | hv <;> subst v
    · rw [B.other_expensive a B.donor_high.symm B.pair_distinct]
      exact hcounts.1
    · exact B.pair_to_low_count (Or.inr rfl)
  refine ⟨fun v _ => B.card v, fun v hv => hownE hv, ?_, ?_⟩
  · intro v hv
    rcases hv with hv | hv <;> subst v
    · unfold OwnCheap
      rw [B.other_bundle B.donor_high.symm B.pair_distinct]
      exact hbad.2.1
    · rw [ownCheap_iff_count]
      have ht := cheap_add_expensive M B.allocation b b
      rw [B.card, B.pair_to_low_count (Or.inr rfl)] at ht
      have hold := cheap_add_expensive M f b b
      have htwo := optimal_bad_target_two_cheap M hf hs ha hb hbad
      omega
  · intro v c hv hc hvc
    rcases hv with hv | hv <;> rcases hc with hc | hc <;> subst v <;> subst c
    · exact False.elim (hvc rfl)
    · rw [hownE (Or.inl rfl), B.pair_to_low_count (Or.inl rfl), hcounts.2]
    · rw [hownE (Or.inr rfl), B.other_expensive b B.donor_high.symm B.pair_distinct,
        pure_observer_expensive M hf.1.1 hb (optimal_bad_source_pure M hf hs ha hb hbad), hcounts.1]
    · exact False.elim (hvc rfl)

theorem outside_to_pair_bound (B : IsolatedSwap M S f a b k) {f₀ : E → A} {q : ℕ}
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) {v c : A}
    (hv : v ∈ B.outside) (hc : c = a ∨ c = b) :
    (bundle B.allocation c).card ≤ expensiveCount M B.allocation v c + 1 := by
  have hvs := Finset.mem_sdiff.mp hv
  have hva : v ≠ a := by intro ht; exact hvs.2 (by simp [ht])
  have hvb : v ≠ b := by intro ht; exact hvs.2 (by simp [ht])
  rcases hc with hc | hc <;> subst c
  · rw [B.card, B.other_expensive v B.donor_high.symm B.pair_distinct,
      pure_outside_expensive M hf.1.1 B.pair_distinct
        (optimal_bad_source_pure M hf hs ha hb hbad) hvs.1 hva hvb]
    omega
  · have ht := exchange_expensive_right M f B.chore_distinct B.owner_distinct v
    rw [B.secondOwner, ite_eq_right (two_cheap_third M B.pair_distinct B.highCheap B.lowCheap hva hvb),
      pure_outside_expensive M hf.1.1 B.pair_distinct.symm
        (minimum_bad_target_pure M (hf.energyMinimum M) hs ha hb hbad) hvs.1 hvb hva] at ht
    change (expensiveCount M B.allocation v b : ℤ) = (bundle f b).card - 1 +
      (if M.Cheap v B.firstChore then 0 else 1) at ht
    rw [B.card]
    split_ifs at ht <;> omega

theorem feasible_pair_bundle (B : IsolatedSwap M S f a b k) {g : E → A}
    (hg : Feasible B.frozenModel B.outside B.allocation g) {v : A} (hv : v = a ∨ v = b) :
    bundle g v = bundle B.allocation v := by
  apply feasible_outside_bundle B.frozenModel hg
  rcases hv with hv | hv <;> subst v <;> simp [outside]

theorem feasible_pair_to_outside (B : IsolatedSwap M S f a b k)
    (hz : ∀ v ∈ B.outside, expensiveCount M f v v = 0) {g : E → A}
    (hg : Feasible B.frozenModel B.outside B.allocation g) {v c : A}
    (hv : v = a ∨ v = b) (hc : c ∈ B.outside) :
    (bundle g c).card ≤ expensiveCount M g v c + 1 := by
  have hsub : (bundle g c).filter (M.Cheap v) ⊆ {B.secondChore} := by
    intro e he
    have hec := Finset.mem_filter.mp he
    have hin : g e ∈ B.outside := by rwa [(mem_bundle g c e).mp hec.1]
    have horig := feasible_original_inside B.frozenModel hg hin
    exact Finset.mem_singleton.mpr (B.pair_cheap_inside hz horig hv hec.2)
  have hcard : cheapCount M g v c ≤ 1 := by
    have ht := Finset.card_le_card hsub
    simpa only [cheapCount, Finset.card_singleton] using ht
  have hsum := cheap_add_expensive M g v c
  omega

end IsolatedSwap

end ResearchMain.Chores
