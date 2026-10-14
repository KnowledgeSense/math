import MainTheorems.Chores.ShortDonor

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure LongDonorTransfer (M : TwoCheapModel A E) (S : Finset A) (f : E → A)
    (a b k : A) where
  donor : ExchangeData M S f a k
  pairChore : E
  pairOwner : f pairChore = b
  highCheap : M.Cheap a pairChore
  lowCheap : M.Cheap b pairChore
  high_ne_low : a ≠ b
  donor_ne_low : k ≠ b
  low_mem : b ∈ S

namespace LongDonorTransfer

variable {M : TwoCheapModel A E} {S : Finset A} {f : E → A} {a b k : A}

def intermediate (T : LongDonorTransfer M S f a b k) : E → A :=
  transfer f T.donor.secondChore a

def allocation (T : LongDonorTransfer M S f a b k) : E → A :=
  exchange T.intermediate T.donor.firstChore T.pairChore

omit [Fintype E] [DecidableEq A] in
theorem first_owner (T : LongDonorTransfer M S f a b k) :
    T.intermediate T.donor.firstChore = a := by
  rw [intermediate, transfer_other f a T.donor.chore_distinct, T.donor.firstOwner]

omit [Fintype E] [DecidableEq A] in
theorem pair_owner (T : LongDonorTransfer M S f a b k) :
    T.intermediate T.pairChore = b := by
  rw [intermediate, transfer_other f a]
  · exact T.pairOwner
  · intro h
    exact T.donor_ne_low ((T.donor.secondOwner).symm.trans ((congrArg f h.symm).trans T.pairOwner))

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem chore_distinct (T : LongDonorTransfer M S f a b k) : T.donor.firstChore ≠ T.pairChore := by
  intro h
  exact T.high_ne_low ((T.donor.firstOwner).symm.trans ((congrArg f h).trans T.pairOwner))

omit [Fintype E] [DecidableEq A] in
theorem owner_distinct (T : LongDonorTransfer M S f a b k) :
    T.intermediate T.donor.firstChore ≠ T.intermediate T.pairChore := by
  rw [T.first_owner, T.pair_owner]
  exact T.high_ne_low

theorem high_card (T : LongDonorTransfer M S f a b k) :
    (bundle T.allocation a).card = (bundle f a).card + 1 := by
  rw [allocation, exchange_bundle_card, intermediate]
  exact transfer_target_card f T.donor.secondChore (by rw [T.donor.secondOwner]; exact T.donor.distinct.symm)

theorem low_bundle (T : LongDonorTransfer M S f a b k) :
    bundle T.allocation b = insert T.donor.firstChore ((bundle f b).erase T.pairChore) := by
  have ht := exchange_bundle_right T.intermediate T.chore_distinct T.owner_distinct
  rw [T.pair_owner] at ht
  rw [allocation, ht, intermediate, transfer_other_bundle f T.donor.secondChore]
  · simpa only [T.donor.secondOwner] using T.donor_ne_low.symm
  · exact T.high_ne_low.symm

theorem low_card (T : LongDonorTransfer M S f a b k) :
    (bundle T.allocation b).card = (bundle f b).card := by
  rw [allocation, exchange_bundle_card, intermediate,
    transfer_other_bundle f T.donor.secondChore]
  · simpa only [T.donor.secondOwner] using T.donor_ne_low.symm
  · exact T.high_ne_low.symm

theorem donor_bundle (T : LongDonorTransfer M S f a b k) :
    bundle T.allocation k = (bundle f k).erase T.donor.secondChore := by
  rw [allocation, exchange_bundle_other T.intermediate]
  · have ht := transfer_source_bundle f T.donor.secondChore
      (by rw [T.donor.secondOwner]; exact T.donor.distinct.symm)
    simpa only [intermediate, T.donor.secondOwner] using ht
  · rw [T.first_owner]
    exact T.donor.distinct.symm
  · rw [T.pair_owner]
    exact T.donor_ne_low

theorem donor_card (T : LongDonorTransfer M S f a b k) :
    (bundle T.allocation k).card + 1 = (bundle f k).card := by
  rw [T.donor_bundle]
  exact Finset.card_erase_add_one ((mem_bundle f k _).mpr T.donor.secondOwner)

theorem other_bundle (T : LongDonorTransfer M S f a b k) {c : A}
    (hca : c ≠ a) (hcb : c ≠ b) (hck : c ≠ k) :
    bundle T.allocation c = bundle f c := by
  rw [allocation, exchange_bundle_other T.intermediate]
  · apply transfer_other_bundle f T.donor.secondChore
    · simpa only [T.donor.secondOwner] using hck
    · exact hca
  · rwa [T.first_owner]
  · rwa [T.pair_owner]

theorem high_cost (T : LongDonorTransfer M S f a b k) (r : ℝ) (v : A) :
    bundleCost M r v (bundle T.allocation a) + itemCost M r v T.donor.firstChore =
      bundleCost M r v (bundle f a) + itemCost M r v T.donor.secondChore +
        itemCost M r v T.pairChore := by
  have ht := exchange_sum_left (itemCost M r v) T.intermediate T.chore_distinct T.owner_distinct
  change bundleCost M r v (bundle T.allocation (T.intermediate T.donor.firstChore)) =
    bundleCost M r v (bundle T.intermediate (T.intermediate T.donor.firstChore)) -
      itemCost M r v T.donor.firstChore + itemCost M r v T.pairChore at ht
  rw [T.first_owner] at ht
  have hi := transfer_target_cost M r f T.donor.secondChore
    (by rw [T.donor.secondOwner]; exact T.donor.distinct.symm) v
  change bundleCost M r v (bundle T.intermediate a) =
    bundleCost M r v (bundle f a) + itemCost M r v T.donor.secondChore at hi
  rw [hi] at ht
  linarith

theorem low_cost (T : LongDonorTransfer M S f a b k) (r : ℝ) (v : A) :
    bundleCost M r v (bundle T.allocation b) + itemCost M r v T.pairChore =
      bundleCost M r v (bundle f b) + itemCost M r v T.donor.firstChore := by
  have ht := exchange_sum_right (itemCost M r v) T.intermediate T.chore_distinct T.owner_distinct
  change bundleCost M r v (bundle T.allocation (T.intermediate T.pairChore)) =
    bundleCost M r v (bundle T.intermediate (T.intermediate T.pairChore)) -
      itemCost M r v T.pairChore + itemCost M r v T.donor.firstChore at ht
  rw [T.pair_owner, intermediate, transfer_other_bundle f T.donor.secondChore
    (by simpa only [T.donor.secondOwner] using T.donor_ne_low.symm) T.high_ne_low.symm] at ht
  linarith

theorem donor_cost (T : LongDonorTransfer M S f a b k) (r : ℝ) (v : A) :
    bundleCost M r v (bundle T.allocation k) + itemCost M r v T.donor.secondChore =
      bundleCost M r v (bundle f k) := by
  have ht := transfer_source_cost M r f T.donor.secondChore
    (by rw [T.donor.secondOwner]; exact T.donor.distinct.symm) v
  rw [T.donor.secondOwner] at ht
  rw [T.donor_bundle]
  have hbun : bundle (transfer f T.donor.secondChore a) k =
      (bundle f k).erase T.donor.secondChore := by
    simpa only [T.donor.secondOwner] using transfer_source_bundle f T.donor.secondChore
      (by rw [T.donor.secondOwner]; exact T.donor.distinct.symm)
  rw [hbun] at ht
  exact ht

end LongDonorTransfer

end ResearchMain.Chores
