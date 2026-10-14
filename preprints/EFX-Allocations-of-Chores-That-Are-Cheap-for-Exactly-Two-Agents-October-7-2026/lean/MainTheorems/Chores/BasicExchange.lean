import MainTheorems.Chores.EnergyExchange

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure ExchangeData (M : TwoCheapModel A E) (S : Finset A) (f : E → A) (a b : A) where
  firstChore : E
  secondChore : E
  firstOwner : f firstChore = a
  secondOwner : f secondChore = b
  source_mem : a ∈ S
  target_mem : b ∈ S
  distinct : a ≠ b
  filler : Filler M S firstChore
  sourceCheap : M.Cheap a secondChore
  targetCheap : M.Cheap b secondChore

namespace ExchangeData

variable {M : TwoCheapModel A E} {S : Finset A} {f : E → A} {a b : A}

def allocation (B : ExchangeData M S f a b) : E → A :=
  exchange f B.firstChore B.secondChore

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem chore_distinct (B : ExchangeData M S f a b) : B.firstChore ≠ B.secondChore := by
  intro h
  exact B.distinct (B.firstOwner.symm.trans ((congrArg f h).trans B.secondOwner))

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem owner_distinct (B : ExchangeData M S f a b) : f B.firstChore ≠ f B.secondChore := by
  simpa only [B.firstOwner, B.secondOwner] using B.distinct

theorem feasible (B : ExchangeData M S f a b) {f₀ : E → A} (hf : Feasible M S f₀ f) :
    Feasible M S f₀ B.allocation := by
  apply feasible_exchange M hf
  · rw [B.firstOwner]
    exact B.source_mem
  · rw [B.secondOwner]
    exact B.target_mem
  · exact B.filler
  · rw [B.firstOwner]
    exact B.sourceCheap

theorem card (B : ExchangeData M S f a b) (c : A) :
    (bundle B.allocation c).card = (bundle f c).card :=
  exchange_bundle_card f B.firstChore B.secondChore c

theorem source_bundle (B : ExchangeData M S f a b) :
    bundle B.allocation a = insert B.secondChore ((bundle f a).erase B.firstChore) := by
  simpa only [allocation, B.firstOwner] using exchange_bundle_left f B.chore_distinct B.owner_distinct

theorem target_bundle (B : ExchangeData M S f a b) :
    bundle B.allocation b = insert B.firstChore ((bundle f b).erase B.secondChore) := by
  simpa only [allocation, B.secondOwner] using exchange_bundle_right f B.chore_distinct B.owner_distinct

theorem other_bundle (B : ExchangeData M S f a b) {c : A} (hca : c ≠ a) (hcb : c ≠ b) :
    bundle B.allocation c = bundle f c := by
  apply exchange_bundle_other
  · simpa only [B.firstOwner] using hca
  · simpa only [B.secondOwner] using hcb

theorem source_own_expensive (B : ExchangeData M S f a b) :
    expensiveCount M B.allocation a a + 1 = expensiveCount M f a a := by
  have h := exchange_expensive_left M f B.chore_distinct B.owner_distinct a
  rw [B.firstOwner, ite_eq_right (filler_not_cheap M B.source_mem B.filler),
    ite_eq_left B.sourceCheap] at h
  change (expensiveCount M B.allocation a a : ℤ) = expensiveCount M f a a - 1 + 0 at h
  omega

theorem target_own_expensive (B : ExchangeData M S f a b) :
    expensiveCount M B.allocation b b = expensiveCount M f b b + 1 := by
  have h := exchange_expensive_right M f B.chore_distinct B.owner_distinct b
  rw [B.secondOwner, ite_eq_right (filler_not_cheap M B.target_mem B.filler),
    ite_eq_left B.targetCheap] at h
  change (expensiveCount M B.allocation b b : ℤ) = expensiveCount M f b b - 0 + 1 at h
  omega

theorem source_sees_target (B : ExchangeData M S f a b) :
    expensiveCount M B.allocation a b = expensiveCount M f a b + 1 := by
  have h := exchange_expensive_right M f B.chore_distinct B.owner_distinct a
  rw [B.secondOwner, ite_eq_right (filler_not_cheap M B.source_mem B.filler),
    ite_eq_left B.sourceCheap] at h
  change (expensiveCount M B.allocation a b : ℤ) = expensiveCount M f a b - 0 + 1 at h
  omega

theorem target_sees_source (B : ExchangeData M S f a b) :
    expensiveCount M B.allocation b a + 1 = expensiveCount M f b a := by
  have h := exchange_expensive_left M f B.chore_distinct B.owner_distinct b
  rw [B.firstOwner, ite_eq_right (filler_not_cheap M B.target_mem B.filler),
    ite_eq_left B.targetCheap] at h
  change (expensiveCount M B.allocation b a : ℤ) = expensiveCount M f b a - 1 + 0 at h
  omega

theorem other_expensive (B : ExchangeData M S f a b) (c : A) {d : A}
    (hda : d ≠ a) (hdb : d ≠ b) :
    expensiveCount M B.allocation c d = expensiveCount M f c d := by
  rw [expensiveCount, B.other_bundle hda hdb]
  rfl

theorem energy_same (B : ExchangeData M S f a b)
    (hcounts : expensiveCount M f a a = expensiveCount M f b b + 1) :
    energy M S B.allocation = energy M S f := by
  have h := energy_exchange M B.chore_distinct B.owner_distinct
    (by rw [B.firstOwner]; exact B.source_mem)
    (by rw [B.secondOwner]; exact B.target_mem) B.filler
    (by rw [B.firstOwner]; exact B.sourceCheap)
    (by rw [B.secondOwner]; exact B.targetCheap)
  rw [B.firstOwner, B.secondOwner, hcounts] at h
  change energy M S B.allocation + 2 * (expensiveCount M f b b + 1) =
    energy M S f + 2 * expensiveCount M f b b + 2 at h
  omega

theorem target_pure (B : ExchangeData M S f a b) (hp : Pure M f b a) :
    Pure M B.allocation b a := by
  intro e he hc
  rw [B.target_bundle] at he
  rcases Finset.mem_insert.mp he with h | h
  · subst e
    exact False.elim ((filler_not_cheap M B.target_mem B.filler) hc)
  · exact hp e (Finset.mem_of_mem_erase h) hc

theorem source_pure (B : ExchangeData M S f a b) (hp : Pure M f a b) :
    Pure M B.allocation a b := by
  intro e he hc
  rw [B.source_bundle] at he
  rcases Finset.mem_insert.mp he with h | h
  · subst e
    exact B.targetCheap
  · exact hp e (Finset.mem_of_mem_erase h) hc

theorem source_cheap_count (B : ExchangeData M S f a b) :
    cheapCount M B.allocation a a = cheapCount M f a a + 1 := by
  have hold := cheap_add_expensive M f a a
  have hnew := cheap_add_expensive M B.allocation a a
  rw [B.card] at hnew
  have he := B.source_own_expensive
  omega

theorem target_cheap_count (B : ExchangeData M S f a b) :
    cheapCount M B.allocation b b + 1 = cheapCount M f b b := by
  have hold := cheap_add_expensive M f b b
  have hnew := cheap_add_expensive M B.allocation b b
  rw [B.card] at hnew
  have he := B.target_own_expensive
  omega

theorem source_mixed (B : ExchangeData M S f a b) (hn : ¬Pure M f a b) :
    Mixed M B.allocation a := by
  classical
  unfold Pure at hn
  push Not at hn
  obtain ⟨e, he, ha, hb⟩ := hn
  have hefirst : e ≠ B.firstChore := by
    intro h
    subst e
    exact (filler_not_cheap M B.source_mem B.filler) ha
  have hemem : e ∈ bundle B.allocation a := by
    rw [B.source_bundle]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hefirst, he⟩)
  have hdmem : B.secondChore ∈ bundle B.allocation a := by
    rw [B.source_bundle]
    exact Finset.mem_insert_self _ _
  refine ⟨e, hemem, B.secondChore, hdmem, ha, B.sourceCheap, ?_⟩
  rw [otherEndpoint_eq M B.distinct B.sourceCheap B.targetCheap]
  intro h
  have hcheap := (cheap_otherEndpoint M ha).1
  rw [h] at hcheap
  exact hb hcheap

end ExchangeData

omit [DecidableEq E] in
theorem exists_basic_exchange (M : TwoCheapModel A E) {S : Finset A} {f : E → A} {q : ℕ}
    (hf : Separated M S f) (hs : ∀ v, q ≤ (bundle f v).card ∧ (bundle f v).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) :
    Nonempty (ExchangeData M S f a b) := by
  obtain ⟨e, he, hecheap⟩ := own_expensive_exists M (bad_expensive_positive M hbad)
  obtain ⟨d, hd, hdcheap⟩ := bad_target_cheap M hbad hs
  have heq := (mem_bundle f a e).mp he
  have hdq := (mem_bundle f b d).mp hd
  refine ⟨⟨e, d, heq, hdq, ha, hb, hbad.1, ?_, hdcheap, ?_⟩⟩
  · exact separated_expensive_filler M hf (e := e) (by rw [heq]; exact hecheap)
  · have h := separated_owner_cheap M hf ha hdcheap
    rwa [hdq] at h

end ResearchMain.Chores
