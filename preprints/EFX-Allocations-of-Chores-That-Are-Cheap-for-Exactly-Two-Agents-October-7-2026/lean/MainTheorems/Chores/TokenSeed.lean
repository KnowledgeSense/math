import MainTheorems.Chores.TokenReady
import MainTheorems.Chores.ThreeCycle

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure TokenSeed {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    (P : TokenReady M S f₀ q k) where
  cycle : ThreeCycle P.allocation P.high P.low k
  high_filler : Filler M S cycle.highChore
  low_highCheap : M.Cheap P.high cycle.lowChore
  low_ownCheap : M.Cheap P.low cycle.lowChore
  donor_highCheap : M.Cheap P.high cycle.donorChore
  donor_ownCheap : M.Cheap k cycle.donorChore

theorem exists_token_seed {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    (P : TokenReady M S f₀ q k) : Nonempty (TokenSeed P) := by
  obtain ⟨e, he, heCheap⟩ := own_expensive_exists M (bad_expensive_positive M P.unique_bad.1)
  obtain ⟨d, hd, hdCheap⟩ := bad_target_ownCheap M P.optimal.1.1 P.size P.high_mem P.unique_bad.1
  have hdHigh := minimum_bad_target_pure M (P.optimal.energyMinimum M) P.size
    P.high_mem P.low_mem P.unique_bad.1 d hd hdCheap
  have hOwnK : OwnCheap M P.allocation k := by
    rw [ownCheap_iff_count]
    have ht := P.donor_cheap
    omega
  obtain ⟨g, hg, hgCheap⟩ := hOwnK
  let C : ThreeCycle P.allocation P.high P.low k :=
    { highChore := e
      lowChore := d
      donorChore := g
      highOwner := (mem_bundle P.allocation P.high e).mp he
      lowOwner := (mem_bundle P.allocation P.low d).mp hd
      donorOwner := (mem_bundle P.allocation k g).mp hg
      high_ne_low := P.unique_bad.1.1
      high_ne_donor := P.donor_high.symm
      low_ne_donor := P.donor_low.symm }
  have hf : Filler M S e := separated_expensive_filler M P.optimal.1.1
    (by rw [(mem_bundle P.allocation P.high e).mp he]; exact heCheap)
  exact ⟨⟨C, hf, hdHigh, hdCheap, P.donor_pure g hg hgCheap, hgCheap⟩⟩

namespace TokenSeed

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {P : TokenReady M S f₀ q k}

theorem high_count (B : TokenSeed P) :
    expensiveCount M B.cycle.allocation P.high P.high = expensiveCount M P.allocation P.low P.low := by
  have ht := B.cycle.high_expensive_balance M P.high
  rw [ite_eq_right (filler_not_cheap M P.high_mem B.high_filler), ite_eq_left B.donor_highCheap,
    add_zero] at ht
  have hc := (minimum_bad_counts M (P.optimal.energyMinimum M) P.size
    P.high_mem P.low_mem P.unique_bad.1).1
  omega

theorem low_count (B : TokenSeed P) :
    expensiveCount M B.cycle.allocation P.low P.low = expensiveCount M P.allocation P.low P.low + 1 := by
  have ht := B.cycle.low_expensive_balance M P.low
  simpa only [ite_eq_left B.low_ownCheap, add_zero,
    ite_eq_right (filler_not_cheap M P.low_mem B.high_filler)] using ht

theorem donor_count (B : TokenSeed P) :
    expensiveCount M B.cycle.allocation k k = expensiveCount M P.allocation P.low P.low + 2 := by
  have hn := two_cheap_third M P.unique_bad.1.1 B.low_highCheap B.low_ownCheap P.donor_high P.donor_low
  have ht := B.cycle.donor_expensive_balance M k
  rw [ite_eq_left B.donor_ownCheap, add_zero, ite_eq_right hn] at ht
  have hc := P.donor_count
  omega

theorem own_cheap (B : TokenSeed P) {v : A} (hv : v = P.high ∨ v = P.low ∨ v = k) :
    OwnCheap M B.cycle.allocation v := by
  rw [ownCheap_iff_count]
  have hsum := cheap_add_expensive M B.cycle.allocation v v
  rw [B.cycle.card] at hsum
  have hsz := (P.size v).1
  have hl := P.low_bound
  rcases hv with hv | hv | hv <;> subst v
  · rw [B.high_count] at hsum
    omega
  · rw [B.low_count] at hsum
    omega
  · rw [B.donor_count] at hsum
    omega

theorem high_mixed (B : TokenSeed P) : Mixed M B.cycle.allocation P.high := by
  obtain ⟨e, he, heCheap⟩ := P.unique_bad.1.2.1
  have hen : e ≠ B.cycle.highChore := by
    intro ht
    subst e
    exact filler_not_cheap M P.high_mem B.high_filler heCheap
  have heNew : e ∈ bundle B.cycle.allocation P.high := by
    rw [B.cycle.high_bundle]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hen, he⟩)
  have hdNew : B.cycle.donorChore ∈ bundle B.cycle.allocation P.high := by
    rw [B.cycle.high_bundle]
    exact Finset.mem_insert_self _ _
  have heLow := optimal_bad_source_pure M P.optimal P.size P.high_mem P.low_mem P.unique_bad.1 e he heCheap
  refine ⟨e, heNew, B.cycle.donorChore, hdNew, heCheap, B.donor_highCheap, ?_⟩
  rw [otherEndpoint_eq M P.unique_bad.1.1 heCheap heLow,
    otherEndpoint_eq M P.donor_high.symm B.donor_highCheap B.donor_ownCheap]
  exact P.donor_low.symm

theorem donor_pure (B : TokenSeed P) : Pure M B.cycle.allocation k P.high := by
  intro e he hc
  rw [B.cycle.donor_bundle] at he
  rcases Finset.mem_insert.mp he with he | he
  · subst e
    exact False.elim (two_cheap_third M P.unique_bad.1.1 B.low_highCheap B.low_ownCheap
      P.donor_high P.donor_low hc)
  · exact P.donor_pure e (Finset.mem_of_mem_erase he) hc

end TokenSeed

end ResearchMain.Chores
