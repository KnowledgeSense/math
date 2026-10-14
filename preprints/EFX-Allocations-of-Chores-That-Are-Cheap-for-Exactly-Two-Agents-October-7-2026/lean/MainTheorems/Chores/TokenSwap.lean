import MainTheorems.Chores.LocalExpensive
import MainTheorems.Chores.RotatingPairs

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure TokenSwap (M : TwoCheapModel A E) (T : Finset A) (f : E → A) (v w : A) where
  token : E
  chore : E
  tokenOwner : f token = v
  choreOwner : f chore = w
  source_mem : v ∈ T
  target_mem : w ∈ T
  distinct : v ≠ w
  token_uniform : Filler M T token
  sourceCheap : M.Cheap v chore
  targetCheap : M.Cheap w chore

namespace TokenSwap

variable {M : TwoCheapModel A E} {T : Finset A} {f : E → A} {v w : A}

def allocation (B : TokenSwap M T f v w) : E → A := exchange f B.token B.chore

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem chore_distinct (B : TokenSwap M T f v w) : B.token ≠ B.chore := by
  intro ht
  exact B.distinct (B.tokenOwner.symm.trans ((congrArg f ht).trans B.choreOwner))

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem owner_distinct (B : TokenSwap M T f v w) : f B.token ≠ f B.chore := by
  simpa only [B.tokenOwner, B.choreOwner] using B.distinct

omit [Fintype E] [DecidableEq A] in
theorem token_owner (B : TokenSwap M T f v w) : B.allocation B.token = w := by
  rw [allocation, exchange_left, B.choreOwner]

theorem card (B : TokenSwap M T f v w) (u : A) : (bundle B.allocation u).card = (bundle f u).card :=
  exchange_bundle_card f B.token B.chore u

theorem source_bundle (B : TokenSwap M T f v w) :
    bundle B.allocation v = insert B.chore ((bundle f v).erase B.token) := by
  have ht := exchange_bundle_left f B.chore_distinct B.owner_distinct
  simpa only [allocation, B.tokenOwner] using ht

theorem target_bundle (B : TokenSwap M T f v w) :
    bundle B.allocation w = insert B.token ((bundle f w).erase B.chore) := by
  have ht := exchange_bundle_right f B.chore_distinct B.owner_distinct
  simpa only [allocation, B.choreOwner] using ht

theorem other_bundle (B : TokenSwap M T f v w) {u : A} (huv : u ≠ v) (huw : u ≠ w) :
    bundle B.allocation u = bundle f u := by
  apply exchange_bundle_other
  · simpa only [B.tokenOwner] using huv
  · simpa only [B.choreOwner] using huw

theorem source_count (B : TokenSwap M T f v w) :
    expensiveCount M B.allocation v v + 1 = expensiveCount M f v v := by
  have ht := exchange_expensive_left M f B.chore_distinct B.owner_distinct v
  rw [B.tokenOwner, ite_eq_right (filler_not_cheap M B.source_mem B.token_uniform),
    ite_eq_left B.sourceCheap] at ht
  change (expensiveCount M B.allocation v v : ℤ) = expensiveCount M f v v - 1 + 0 at ht
  omega

theorem target_count (B : TokenSwap M T f v w) :
    expensiveCount M B.allocation w w = expensiveCount M f w w + 1 := by
  have ht := exchange_expensive_right M f B.chore_distinct B.owner_distinct w
  rw [B.choreOwner, ite_eq_left B.targetCheap,
    ite_eq_right (filler_not_cheap M B.target_mem B.token_uniform)] at ht
  change (expensiveCount M B.allocation w w : ℤ) = expensiveCount M f w w - 0 + 1 at ht
  omega

theorem source_to_target (B : TokenSwap M T f v w) :
    expensiveCount M B.allocation v w = expensiveCount M f v w + 1 := by
  have ht := exchange_expensive_right M f B.chore_distinct B.owner_distinct v
  rw [B.choreOwner, ite_eq_left B.sourceCheap,
    ite_eq_right (filler_not_cheap M B.source_mem B.token_uniform)] at ht
  change (expensiveCount M B.allocation v w : ℤ) = expensiveCount M f v w - 0 + 1 at ht
  omega

theorem outsider_expensive (B : TokenSwap M T f v w) {u : A}
    (hu : u ∈ T) (huv : u ≠ v) (huw : u ≠ w) (c : A) :
    expensiveCount M B.allocation u c = expensiveCount M f u c := by
  have hn₁ := filler_not_cheap M hu B.token_uniform
  have hn₂ := two_cheap_third M B.distinct B.sourceCheap B.targetCheap huv huw
  by_cases hcv : c = v
  · subst c
    have ht := exchange_expensive_left M f B.chore_distinct B.owner_distinct u
    rw [B.tokenOwner, ite_eq_right hn₁, ite_eq_right hn₂] at ht
    change (expensiveCount M B.allocation u v : ℤ) = expensiveCount M f u v - 1 + 1 at ht
    omega
  · by_cases hcw : c = w
    · subst c
      have ht := exchange_expensive_right M f B.chore_distinct B.owner_distinct u
      rw [B.choreOwner, ite_eq_right hn₂, ite_eq_right hn₁] at ht
      change (expensiveCount M B.allocation u w : ℤ) = expensiveCount M f u w - 1 + 1 at ht
      omega
    · rw [expensiveCount, B.other_bundle hcv hcw]
      rfl

theorem source_cheap_subset (B : TokenSwap M T f v w) {e : E}
    (he : e ∈ bundle f v) (hc : M.Cheap v e) : e ∈ bundle B.allocation v := by
  have hn : e ≠ B.token := by
    intro ht
    subst e
    exact filler_not_cheap M B.source_mem B.token_uniform hc
  rw [B.source_bundle]
  exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hn, he⟩)

theorem source_mixed_preserved (B : TokenSwap M T f v w) (hm : Mixed M f v) :
    Mixed M B.allocation v := by
  obtain ⟨e, he, d, hd, hec, hdc, hne⟩ := hm
  exact ⟨e, B.source_cheap_subset he hec, d, B.source_cheap_subset hd hdc, hec, hdc, hne⟩

theorem source_mixed_of_pure (B : TokenSwap M T f v w) {p : A}
    (hvp : v ≠ p) (hpw : p ≠ w) (hp : Pure M f v p) (hc : OwnCheap M f v) :
    Mixed M B.allocation v := by
  obtain ⟨e, he, heCheap⟩ := hc
  have heP := hp e he heCheap
  have hdNew : B.chore ∈ bundle B.allocation v := by rw [B.source_bundle]; exact Finset.mem_insert_self _ _
  refine ⟨e, B.source_cheap_subset he heCheap, B.chore, hdNew, heCheap, B.sourceCheap, ?_⟩
  rw [otherEndpoint_eq M hvp heCheap heP, otherEndpoint_eq M B.distinct B.sourceCheap B.targetCheap]
  exact hpw

end TokenSwap

end ResearchMain.Chores
