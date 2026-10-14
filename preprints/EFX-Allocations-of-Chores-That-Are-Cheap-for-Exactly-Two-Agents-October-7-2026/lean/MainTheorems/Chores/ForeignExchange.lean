import MainTheorems.Chores.ScalarCriteria

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure ForeignExchange (M : TwoCheapModel A E) (S : Finset A) (f : E → A) (a b k : A) where
  firstChore : E
  secondChore : E
  firstOwner : f firstChore = k
  secondOwner : f secondChore = b
  high_mem : a ∈ S
  low_mem : b ∈ S
  donor_mem : k ∈ S
  pair_distinct : a ≠ b
  donor_high : k ≠ a
  donor_low : k ≠ b
  filler : Filler M S firstChore
  highCheap : M.Cheap a secondChore
  lowCheap : M.Cheap b secondChore

namespace ForeignExchange

variable {M : TwoCheapModel A E} {S : Finset A} {f : E → A} {a b k : A}

def allocation (B : ForeignExchange M S f a b k) : E → A :=
  exchange f B.firstChore B.secondChore

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem chore_distinct (B : ForeignExchange M S f a b k) : B.firstChore ≠ B.secondChore := by
  intro h
  exact B.donor_low (B.firstOwner.symm.trans ((congrArg f h).trans B.secondOwner))

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem owner_distinct (B : ForeignExchange M S f a b k) : f B.firstChore ≠ f B.secondChore := by
  simpa only [B.firstOwner, B.secondOwner] using B.donor_low

theorem card (B : ForeignExchange M S f a b k) (c : A) :
    (bundle B.allocation c).card = (bundle f c).card :=
  exchange_bundle_card f B.firstChore B.secondChore c

theorem other_bundle (B : ForeignExchange M S f a b k) {c : A} (hck : c ≠ k) (hcb : c ≠ b) :
    bundle B.allocation c = bundle f c := by
  apply exchange_bundle_other
  · simpa only [B.firstOwner] using hck
  · simpa only [B.secondOwner] using hcb

theorem other_expensive (B : ForeignExchange M S f a b k) (c : A) {d : A}
    (hdk : d ≠ k) (hdb : d ≠ b) :
    expensiveCount M B.allocation c d = expensiveCount M f c d := by
  rw [expensiveCount, B.other_bundle hdk hdb]
  rfl

theorem source_count (B : ForeignExchange M S f a b k) {c : A} (hc : c ∈ S) :
    expensiveCount M B.allocation c k + (if M.Cheap c B.secondChore then 1 else 0) =
      expensiveCount M f c k := by
  have h := exchange_expensive_left M f B.chore_distinct B.owner_distinct c
  rw [B.firstOwner, ite_eq_right (filler_not_cheap M hc B.filler)] at h
  change (expensiveCount M B.allocation c k : ℤ) = expensiveCount M f c k - 1 +
    (if M.Cheap c B.secondChore then 0 else 1) at h
  by_cases hcheap : M.Cheap c B.secondChore <;> simp [hcheap] at h ⊢ <;> omega

theorem target_count (B : ForeignExchange M S f a b k) {c : A} (hc : c ∈ S) :
    expensiveCount M B.allocation c b = expensiveCount M f c b +
      (if M.Cheap c B.secondChore then 1 else 0) := by
  have h := exchange_expensive_right M f B.chore_distinct B.owner_distinct c
  rw [B.secondOwner, ite_eq_right (filler_not_cheap M hc B.filler)] at h
  change (expensiveCount M B.allocation c b : ℤ) = expensiveCount M f c b -
    (if M.Cheap c B.secondChore then 0 else 1) + 1 at h
  by_cases hcheap : M.Cheap c B.secondChore <;> simp [hcheap] at h ⊢ <;> omega

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem outside_not_cheap (B : ForeignExchange M S f a b k) {c : A} (hca : c ≠ a) (hcb : c ≠ b) :
    ¬M.Cheap c B.secondChore :=
  two_cheap_third M B.pair_distinct B.highCheap B.lowCheap hca hcb

theorem donor_expensive (B : ForeignExchange M S f a b k) :
    expensiveCount M B.allocation k k = expensiveCount M f k k := by
  have h := B.source_count B.donor_mem
  simpa only [ite_eq_right (B.outside_not_cheap B.donor_high B.donor_low), add_zero] using h

theorem low_expensive (B : ForeignExchange M S f a b k) :
    expensiveCount M B.allocation b b = expensiveCount M f b b + 1 := by
  simpa only [ite_eq_left B.lowCheap] using B.target_count B.low_mem

theorem high_expensive (B : ForeignExchange M S f a b k) :
    expensiveCount M B.allocation a a = expensiveCount M f a a :=
  B.other_expensive a B.donor_high.symm B.pair_distinct

theorem low_cheap (B : ForeignExchange M S f a b k) :
    cheapCount M B.allocation b b + 1 = cheapCount M f b b := by
  have hold := cheap_add_expensive M f b b
  have hnew := cheap_add_expensive M B.allocation b b
  rw [B.card, B.low_expensive] at hnew
  omega

theorem low_ownCheap (B : ForeignExchange M S f a b k) (htwo : 2 ≤ cheapCount M f b b) :
    OwnCheap M B.allocation b := by
  rw [ownCheap_iff_count]
  have h := B.low_cheap
  omega

theorem high_ownCheap (B : ForeignExchange M S f a b k) (hc : OwnCheap M f a) :
    OwnCheap M B.allocation a := by
  simpa only [OwnCheap, B.other_bundle B.donor_high.symm B.pair_distinct] using hc

theorem outsider_threshold (B : ForeignExchange M S f a b k) (r : ℝ) {c : A} (hcb : c ≠ b) :
    threshold M r B.allocation c = threshold M r f c := by
  apply threshold_eq_of_counts M r (B.card c)
  by_cases hck : c = k
  · subst c
    exact B.donor_expensive
  · exact B.other_expensive c hck hcb

theorem outsider_cost (B : ForeignExchange M S f a b k) (r : ℝ) {c : A}
    (hc : c ∈ S) (hca : c ≠ a) (hcb : c ≠ b) (d : A) :
    bundleCost M r c (bundle B.allocation d) = bundleCost M r c (bundle f d) := by
  apply cost_eq_of_counts M r (B.card d)
  by_cases hdk : d = k
  · subst d
    have h := B.source_count hc
    simpa only [ite_eq_right (B.outside_not_cheap hca hcb), add_zero] using h
  · by_cases hdb : d = b
    · subst d
      simpa only [ite_eq_right (B.outside_not_cheap hca hcb), add_zero] using B.target_count hc
    · exact B.other_expensive c hdk hdb

theorem outsider_expensive (B : ForeignExchange M S f a b k) {c : A}
    (hc : c ∈ S) (hca : c ≠ a) (hcb : c ≠ b) (d : A) :
    expensiveCount M B.allocation c d = expensiveCount M f c d := by
  by_cases hdk : d = k
  · subst d
    have ht := B.source_count hc
    simpa only [ite_eq_right (B.outside_not_cheap hca hcb), add_zero] using ht
  · by_cases hdb : d = b
    · subst d
      simpa only [ite_eq_right (B.outside_not_cheap hca hcb), add_zero] using B.target_count hc
    · exact B.other_expensive c hdk hdb

end ForeignExchange

end ResearchMain.Chores
