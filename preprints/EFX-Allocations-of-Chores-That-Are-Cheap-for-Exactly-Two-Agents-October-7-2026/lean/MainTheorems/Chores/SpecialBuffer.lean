import MainTheorems.Chores.MixedCycles
import MainTheorems.Chores.ForeignExchange

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

theorem special_buffer (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (i : OrdinaryIndex M S f q) (hi : ∀ j : OrdinaryIndex M S f q, j = i)
    (j : SpecialIndex M S f q) : ∃ g : E → A, EFX M r g := by
  classical
  let I : PairIndex M S f := i.val
  let J := SpecialIndex M S f q
  let κ : J ↪ PairIndex M S f := ⟨Subtype.val, Subtype.val_injective⟩
  have hI : expensiveCount M f I.low I.low + 1 ≠ q := i.property
  have hunique (k : PairIndex M S f) (hk : expensiveCount M f k.low k.low + 1 ≠ q) : k = I := by
    exact congrArg Subtype.val (hi ⟨k, hk⟩)
  have hdis (k : J) : I ≠ κ k := by
    intro ht
    exact hI (by rw [ht]; exact k.property)
  have hnotSpecial {v : A} (hv : v = I.high ∨ v = I.low) :
      ∀ k : J, v ≠ (κ k).high ∧ v ≠ (κ k).low :=
    fun k => PairIndex.endpoint_ne M hf hs (hdis k) hv
  have hnotOrdinary (k : PairIndex M S f) (hk : expensiveCount M f k.low k.low + 1 = q)
      {v : A} (hv : v = k.high ∨ v = k.low) : v ≠ I.high ∧ v ≠ I.low := by
    have hne : k ≠ I := by intro ht; subst k; exact hI hk
    exact PairIndex.endpoint_ne M hf hs hne hv
  obtain ⟨B⟩ := selected_special_moves M hf hs κ (fun k => k.property) f (fun _ _ _ => rfl)
  have hpairBundle {c : A} (hc : c = I.high ∨ c = I.low) : bundle B.allocation c = bundle f c :=
    B.other c (hnotSpecial hc)
  have hpairE (v : A) {c : A} (hc : c = I.high ∨ c = I.low) :
      expensiveCount M B.allocation v c = expensiveCount M f v c := by
    rw [expensiveCount, hpairBundle hc]
    rfl
  have hq : 0 < q := by
    have ht := j.property
    omega
  have hepos : 0 < expensiveCount M B.allocation (κ j).high (κ j).high := by
    rw [(B.stats j).high_expensive]
    exact hq
  obtain ⟨e, he, hecheap⟩ := own_expensive_exists M hepos
  have heOrig := B.high_subset j he
  have hefill : Filler M S e := by
    apply separated_expensive_filler M hf.1.1
    rw [(mem_bundle f (κ j).high e).mp heOrig]
    exact hecheap
  obtain ⟨d, hd, hdCheap⟩ := bad_target_ownCheap M hf.1.1 hs I.members.1 I.bad
  have hdHigh := minimum_bad_target_pure M (hf.energyMinimum M) hs I.members.1 I.members.2 I.bad
    d hd hdCheap
  have hz := hnotOrdinary (κ j) j.property (Or.inl rfl)
  let F : ForeignExchange M S B.allocation I.high I.low (κ j).high :=
    { firstChore := e
      secondChore := d
      firstOwner := (mem_bundle B.allocation (κ j).high e).mp he
      secondOwner := (mem_bundle B.allocation I.low d).mp (by rw [hpairBundle (Or.inr rfl)]; exact hd)
      high_mem := I.members.1
      low_mem := I.members.2
      donor_mem := (κ j).members.1
      pair_distinct := I.bad.1
      donor_high := hz.1
      donor_low := hz.2
      filler := hefill
      highCheap := hdHigh
      lowCheap := hdCheap }
  have hordStats : OrdinaryStats M f F.allocation I.high I.low := by
    have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs I.members.1 I.members.2 I.bad).1
    have htwo : 2 ≤ cheapCount M B.allocation I.low I.low := by
      unfold cheapCount
      rw [hpairBundle (Or.inr rfl)]
      exact optimal_bad_target_two_cheap M hf hs I.members.1 I.members.2 I.bad
    have hownHigh : OwnCheap M B.allocation I.high := by
      unfold OwnCheap
      rw [hpairBundle (Or.inl rfl)]
      exact I.bad.2.1
    have hownE {v : A} (hv : v = I.high ∨ v = I.low) :
        expensiveCount M F.allocation v v = expensiveCount M f I.low I.low + 1 := by
      rcases hv with hv | hv <;> subst v
      · rw [F.high_expensive, hpairE I.high (Or.inl rfl)]
        exact hcounts
      · rw [F.low_expensive, hpairE I.low (Or.inr rfl)]
    refine ⟨fun v hv => by rw [F.card, hpairBundle hv], fun v hv => hownE hv, ?_, ?_⟩
    · intro v hv
      rcases hv with hv | hv <;> subst v
      · exact F.high_ownCheap hownHigh
      · exact F.low_ownCheap htwo
    · intro v c hv hc hvc
      rcases hv with hv | hv <;> rcases hc with hc | hc <;> subst v <;> subst c
      · exact False.elim (hvc rfl)
      · rw [hownE (Or.inl rfl)]
        have ht := F.target_count I.members.1
        rw [ite_eq_left hdHigh, hpairE I.high (Or.inr rfl),
          pure_observer_expensive M hf.1.1 I.members.1
            (minimum_bad_target_pure M (hf.energyMinimum M) hs I.members.1 I.members.2 I.bad)] at ht
        exact le_of_eq ht.symm
      · rw [hownE (Or.inr rfl), F.other_expensive I.low hz.1.symm I.bad.1,
          hpairE I.low (Or.inl rfl), pure_observer_expensive M hf.1.1 I.members.2
            (optimal_bad_source_pure M hf hs I.members.1 I.members.2 I.bad), hcounts]
      · exact False.elim (hvc rfl)
  have hsmin (k : J) {c : A} (hc : c = (κ k).high ∨ c = (κ k).low) :
      q ≤ (bundle B.allocation c).card := by
    rcases hc with hc | hc <;> subst c
    · rw [(B.stats k).high_size]
    · rw [(B.stats k).low_size]
      omega
  have hspecStats (k : PairIndex M S f) (hk : expensiveCount M f k.low k.low + 1 = q) :
      SpecialStats M F.allocation k.high k.low q := by
    apply (B.stats ⟨k, hk⟩).of_counts (fun v _ => F.card v)
    intro v c hv _
    have hvS : v ∈ S := hv.elim (fun ht => ht ▸ k.members.1) (fun ht => ht ▸ k.members.2)
    have hvn := hnotOrdinary k hk hv
    exact F.outsider_expensive hvS hvn.1 hvn.2 c
  refine ⟨F.allocation, repaired_pairs_efx M hr hf hs ?_ hspecStats ?_ ?_ ?_⟩
  · intro k hk
    have ht := hunique k hk
    subst k
    exact hordStats
  · intro v hv
    rw [F.other_bundle (hv (κ j)).1 (hv I).2, B.other v (fun k => hv (κ k))]
  · intro k l hkl v c hv hc
    have hvS : v ∈ S := hv.elim (fun ht => ht ▸ k.members.1) (fun ht => ht ▸ k.members.2)
    have hvl := PairIndex.endpoint_ne M hf hs hkl hv
    constructor
    · intro hk
      have hvn := hnotOrdinary k hk hv
      rw [F.outsider_expensive hvS hvn.1 hvn.2 c]
      by_cases hl : expensiveCount M f l.low l.low + 1 = q
      · let t : J := ⟨l, hl⟩
        have ht : expensiveCount M B.allocation v c = (bundle B.allocation c).card :=
          B.whole t v c hvS hvl.1 hvl.2 hc
        rw [ht]
        exact hsmin t hc
      · have ht := hunique l hl
        subst l
        rw [hpairE v hc, PairIndex.outside_expensive M hf hs hvS hvl hc]
        exact (hs c).1
    · intro hk
      have ht := hunique k hk
      subst k
      have hl : expensiveCount M f l.low l.low + 1 = q := by
        by_contra hn
        exact hkl (hunique l hn).symm
      let t : J := ⟨l, hl⟩
      have hwhole : expensiveCount M B.allocation v c = (bundle B.allocation c).card :=
        B.whole t v c hvS hvl.1 hvl.2 hc
      have hsz := hsmin t hc
      have hcb : c ≠ I.low := by
        intro heq
        exact hkl (PairIndex.endpoint_unique M hf hs (Or.inr heq) hc)
      by_cases hcz : c = (κ j).high
      · subst c
        have hcE := F.source_count hvS
        rw [hwhole] at hcE
        split_ifs at hcE <;> omega
      · rw [F.other_expensive v hcz hcb, hwhole]
        omega
  · intro v hvS hvn k c hc
    rw [F.outsider_expensive hvS (hvn I).1 (hvn I).2 c]
    constructor
    · intro hk
      have ht : expensiveCount M B.allocation v c = (bundle B.allocation c).card :=
        B.whole ⟨k, hk⟩ v c hvS (hvn k).1 (hvn k).2 hc
      rw [ht, F.card]
    · intro hk
      have ht := hunique k hk
      subst k
      exact hpairE v hc

end ResearchMain.Chores
