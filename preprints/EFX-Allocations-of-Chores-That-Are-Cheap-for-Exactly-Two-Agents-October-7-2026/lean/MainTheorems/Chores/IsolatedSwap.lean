import MainTheorems.Chores.IsolatedPair
import MainTheorems.Chores.FrozenComparisons

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

omit [DecidableEq E] in
theorem all_cheap_of_expensive_zero (M : TwoCheapModel A E) {f : E → A} {v : A}
    (hv : expensiveCount M f v v = 0) {e : E} (he : e ∈ bundle f v) : M.Cheap v e := by
  by_contra hn
  have ht : 0 < expensiveCount M f v v := Finset.card_pos.mpr
    ⟨e, Finset.mem_filter.mpr ⟨he, hn⟩⟩
  omega

structure IsolatedSwap (M : TwoCheapModel A E) (S : Finset A) (f : E → A) (a b k : A) where
  firstChore : E
  secondChore : E
  firstOwner : f firstChore = k
  secondOwner : f secondChore = b
  donor_mem : k ∈ S
  pair_distinct : a ≠ b
  donor_high : k ≠ a
  donor_low : k ≠ b
  donorCheap : M.Cheap k firstChore
  highCheap : M.Cheap a secondChore
  lowCheap : M.Cheap b secondChore
  isolated : IsolatedPair M a b

namespace IsolatedSwap

variable {M : TwoCheapModel A E} {S : Finset A} {f : E → A} {a b k : A}

def allocation (B : IsolatedSwap M S f a b k) : E → A := exchange f B.firstChore B.secondChore

def outside (_ : IsolatedSwap M S f a b k) : Finset A := S \ {a, b}

def frozenModel (B : IsolatedSwap M S f a b k) : TwoCheapModel A E :=
  freezeExternal M B.outside B.allocation a b B.pair_distinct

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem chore_distinct (B : IsolatedSwap M S f a b k) : B.firstChore ≠ B.secondChore := by
  intro ht
  exact B.donor_low (B.firstOwner.symm.trans ((congrArg f ht).trans B.secondOwner))

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem owner_distinct (B : IsolatedSwap M S f a b k) : f B.firstChore ≠ f B.secondChore := by
  simpa only [B.firstOwner, B.secondOwner] using B.donor_low

theorem card (B : IsolatedSwap M S f a b k) (v : A) :
    (bundle B.allocation v).card = (bundle f v).card :=
  exchange_bundle_card f B.firstChore B.secondChore v

theorem other_bundle (B : IsolatedSwap M S f a b k) {v : A} (hvk : v ≠ k) (hvb : v ≠ b) :
    bundle B.allocation v = bundle f v := by
  apply exchange_bundle_other
  · simpa only [B.firstOwner] using hvk
  · simpa only [B.secondOwner] using hvb

omit [Fintype E] [DecidableEq E] in
theorem donor_outside (B : IsolatedSwap M S f a b k) : k ∈ B.outside := by
  simp only [outside, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨B.donor_mem, not_or.mpr ⟨B.donor_high, B.donor_low⟩⟩

omit [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem first_pair_expensive (B : IsolatedSwap M S f a b k) {v : A} (hv : v = a ∨ v = b) :
    ¬M.Cheap v B.firstChore := by
  intro hc
  have hp : M.Cheap a B.firstChore ∧ M.Cheap b B.firstChore := by
    apply B.isolated
    rcases hv with hv | hv <;> subst v
    · exact Or.inl hc
    · exact Or.inr hc
  exact two_cheap_third M B.pair_distinct hp.1 hp.2 B.donor_high B.donor_low B.donorCheap

omit [Fintype E] [DecidableEq E] in
theorem token_filler (B : IsolatedSwap M S f a b k) : Filler M B.outside B.secondChore := by
  obtain hp | hp := pair_endpoints M B.pair_distinct B.highCheap B.lowCheap
  · simp [Filler, outside, hp.1, hp.2]
  · simp [Filler, outside, hp.1, hp.2]

omit [Fintype E] in
theorem token_inside (B : IsolatedSwap M S f a b k) : B.allocation B.secondChore ∈ B.outside := by
  change exchange f B.firstChore B.secondChore B.secondChore ∈ B.outside
  rw [exchange_right, B.firstOwner]
  exact B.donor_outside

theorem inside_cheap (B : IsolatedSwap M S f a b k)
    (hz : ∀ v ∈ B.outside, expensiveCount M f v v = 0) {e : E}
    (he : B.allocation e ∈ B.outside) (ht : e ≠ B.secondChore) : M.Cheap (B.allocation e) e := by
  have heFirst : e ≠ B.firstChore := by
    intro heq
    subst e
    change exchange f B.firstChore B.secondChore B.firstChore ∈ B.outside at he
    rw [exchange_left, B.secondOwner] at he
    simp [outside] at he
  have ho : B.allocation e = f e := exchange_other f heFirst ht
  rw [ho] at he ⊢
  exact all_cheap_of_expensive_zero M (hz _ he) ((mem_bundle f (f e) e).mpr rfl)

theorem frozen_separated (B : IsolatedSwap M S f a b k)
    (hz : ∀ v ∈ B.outside, expensiveCount M f v v = 0) :
    Separated B.frozenModel B.outside B.allocation := by
  apply frozen_initial_separated M B.outside B.allocation B.pair_distinct
    (by simp [outside]) (by simp [outside])
  intro e he
  by_cases ht : e = B.secondChore
  · subst e
    exact Or.inr B.token_filler
  · exact Or.inl (B.inside_cheap hz he ht)

theorem frozen_filler_iff (B : IsolatedSwap M S f a b k)
    (hz : ∀ v ∈ B.outside, expensiveCount M f v v = 0) {e : E}
    (he : B.allocation e ∈ B.outside) : Filler B.frozenModel B.outside e ↔ e = B.secondChore := by
  change Filler (freezeExternal M B.outside B.allocation a b B.pair_distinct) B.outside e ↔ _
  rw [frozen_filler_inside M B.outside B.allocation a b B.pair_distinct he]
  constructor
  · intro hf
    by_contra ht
    have hc := B.inside_cheap hz he ht
    exact filler_not_cheap M he hf hc
  · intro ht
    subst e
    exact B.token_filler

theorem pair_cheap_inside (B : IsolatedSwap M S f a b k)
    (hz : ∀ v ∈ B.outside, expensiveCount M f v v = 0) {e : E} {v : A}
    (he : B.allocation e ∈ B.outside) (hv : v = a ∨ v = b) (hc : M.Cheap v e) :
    e = B.secondChore := by
  by_contra ht
  have hd := B.inside_cheap hz he ht
  have hp : M.Cheap a e ∧ M.Cheap b e := by
    apply B.isolated
    rcases hv with hv | hv <;> subst v
    · exact Or.inl hc
    · exact Or.inr hc
  have ho := Finset.mem_sdiff.mp he
  have hoa : B.allocation e ≠ a := by intro h; exact ho.2 (by simp [h])
  have hob : B.allocation e ≠ b := by intro h; exact ho.2 (by simp [h])
  exact two_cheap_third M B.pair_distinct hp.1 hp.2 hoa hob hd

end IsolatedSwap

end ResearchMain.Chores
