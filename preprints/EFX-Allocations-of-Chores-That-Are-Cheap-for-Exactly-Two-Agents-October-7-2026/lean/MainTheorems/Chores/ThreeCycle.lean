import MainTheorems.Chores.RotatingPairs

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure ThreeCycle (f : E → A) (a b k : A) where
  highChore : E
  lowChore : E
  donorChore : E
  highOwner : f highChore = a
  lowOwner : f lowChore = b
  donorOwner : f donorChore = k
  high_ne_low : a ≠ b
  high_ne_donor : a ≠ k
  low_ne_donor : b ≠ k

namespace ThreeCycle

variable {f : E → A} {a b k : A}

def intermediate (P : ThreeCycle f a b k) : E → A := exchange f P.lowChore P.donorChore

def allocation (P : ThreeCycle f a b k) : E → A := exchange P.intermediate P.highChore P.donorChore

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem high_low_distinct (P : ThreeCycle f a b k) : P.highChore ≠ P.lowChore := by
  intro ht
  exact P.high_ne_low (P.highOwner.symm.trans ((congrArg f ht).trans P.lowOwner))

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem high_donor_distinct (P : ThreeCycle f a b k) : P.highChore ≠ P.donorChore := by
  intro ht
  exact P.high_ne_donor (P.highOwner.symm.trans ((congrArg f ht).trans P.donorOwner))

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem low_donor_distinct (P : ThreeCycle f a b k) : P.lowChore ≠ P.donorChore := by
  intro ht
  exact P.low_ne_donor (P.lowOwner.symm.trans ((congrArg f ht).trans P.donorOwner))

omit [Fintype E] [DecidableEq A] in
theorem intermediate_high (P : ThreeCycle f a b k) : P.intermediate P.highChore = a := by
  rw [intermediate, exchange_other f P.high_low_distinct P.high_donor_distinct, P.highOwner]

omit [Fintype E] [DecidableEq A] in
theorem intermediate_donor (P : ThreeCycle f a b k) : P.intermediate P.donorChore = b := by
  rw [intermediate, exchange_right, P.lowOwner]

omit [Fintype E] [DecidableEq A] in
theorem token_owner (P : ThreeCycle f a b k) : P.allocation P.lowChore = k := by
  rw [allocation, exchange_other P.intermediate P.high_low_distinct.symm P.low_donor_distinct,
    intermediate, exchange_left, P.donorOwner]

theorem card (P : ThreeCycle f a b k) (v : A) : (bundle P.allocation v).card = (bundle f v).card := by
  rw [allocation, exchange_bundle_card, intermediate, exchange_bundle_card]

theorem high_bundle (P : ThreeCycle f a b k) :
    bundle P.allocation a = insert P.donorChore ((bundle f a).erase P.highChore) := by
  have howners : P.intermediate P.highChore ≠ P.intermediate P.donorChore := by
    rw [P.intermediate_high, P.intermediate_donor]
    exact P.high_ne_low
  have ht := exchange_bundle_left P.intermediate P.high_donor_distinct howners
  rw [P.intermediate_high] at ht
  change bundle P.allocation a = _ at ht
  rw [ht, intermediate, exchange_bundle_other f
    (by rw [P.lowOwner]; exact P.high_ne_low) (by rw [P.donorOwner]; exact P.high_ne_donor)]

theorem low_bundle (P : ThreeCycle f a b k) :
    bundle P.allocation b = insert P.highChore ((bundle f b).erase P.lowChore) := by
  have howners : P.intermediate P.highChore ≠ P.intermediate P.donorChore := by
    rw [P.intermediate_high, P.intermediate_donor]
    exact P.high_ne_low
  have ht := exchange_bundle_right P.intermediate P.high_donor_distinct howners
  rw [P.intermediate_donor] at ht
  change bundle P.allocation b = _ at ht
  have howners₀ : f P.lowChore ≠ f P.donorChore := by rw [P.lowOwner, P.donorOwner]; exact P.low_ne_donor
  have hmid := exchange_bundle_left f P.low_donor_distinct howners₀
  rw [P.lowOwner] at hmid
  change bundle P.intermediate b = _ at hmid
  have hn : P.donorChore ∉ (bundle f b).erase P.lowChore := by
    intro he
    have ho := (mem_bundle f b _).mp (Finset.mem_of_mem_erase he)
    exact P.low_ne_donor (ho.symm.trans P.donorOwner)
  rw [ht, hmid, Finset.erase_insert hn]

theorem donor_bundle (P : ThreeCycle f a b k) :
    bundle P.allocation k = insert P.lowChore ((bundle f k).erase P.donorChore) := by
  have howners : f P.lowChore ≠ f P.donorChore := by rw [P.lowOwner, P.donorOwner]; exact P.low_ne_donor
  have ht := exchange_bundle_right f P.low_donor_distinct howners
  rw [P.donorOwner] at ht
  change bundle P.intermediate k = _ at ht
  rw [allocation, exchange_bundle_other P.intermediate
    (by rw [P.intermediate_high]; exact P.high_ne_donor.symm)
    (by rw [P.intermediate_donor]; exact P.low_ne_donor.symm), ht]

theorem other_bundle (P : ThreeCycle f a b k) {v : A} (hva : v ≠ a) (hvb : v ≠ b) (hvk : v ≠ k) :
    bundle P.allocation v = bundle f v := by
  rw [allocation, exchange_bundle_other P.intermediate
    (by rw [P.intermediate_high]; exact hva) (by rw [P.intermediate_donor]; exact hvb)]
  rw [intermediate, exchange_bundle_other f
    (by rw [P.lowOwner]; exact hvb) (by rw [P.donorOwner]; exact hvk)]

theorem high_expensive_balance (P : ThreeCycle f a b k) (M : TwoCheapModel A E) (v : A) :
    expensiveCount M P.allocation v a + (if M.Cheap v P.highChore then 0 else 1) =
      expensiveCount M f v a + (if M.Cheap v P.donorChore then 0 else 1) := by
  apply replacement_expensive M ((mem_bundle f a _).mpr P.highOwner) ?_ P.high_bundle v
  intro he
  exact P.high_ne_donor (((mem_bundle f a _).mp he).symm.trans P.donorOwner)

theorem low_expensive_balance (P : ThreeCycle f a b k) (M : TwoCheapModel A E) (v : A) :
    expensiveCount M P.allocation v b + (if M.Cheap v P.lowChore then 0 else 1) =
      expensiveCount M f v b + (if M.Cheap v P.highChore then 0 else 1) := by
  apply replacement_expensive M ((mem_bundle f b _).mpr P.lowOwner) ?_ P.low_bundle v
  intro he
  exact P.high_ne_low (P.highOwner.symm.trans ((mem_bundle f b _).mp he))

theorem donor_expensive_balance (P : ThreeCycle f a b k) (M : TwoCheapModel A E) (v : A) :
    expensiveCount M P.allocation v k + (if M.Cheap v P.donorChore then 0 else 1) =
      expensiveCount M f v k + (if M.Cheap v P.lowChore then 0 else 1) := by
  apply replacement_expensive M ((mem_bundle f k _).mpr P.donorOwner) ?_ P.donor_bundle v
  intro he
  exact P.low_ne_donor (P.lowOwner.symm.trans ((mem_bundle f k _).mp he))

end ThreeCycle

end ResearchMain.Chores
