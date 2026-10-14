import MainTheorems.Chores.RotatingPairs
import MainTheorems.Chores.RepairStats

namespace ResearchMain.Chores

variable {A E I : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure CycleResult (M : TwoCheapModel A E) (S : Finset A) (f : E → A)
    (ι : I ↪ PairIndex M S f) where
  allocation : E → A
  size : ∀ c, (bundle allocation c).card = (bundle f c).card
  stats : ∀ i, OrdinaryStats M f allocation (ι i).high (ι i).low
  other : ∀ c, (∀ i, c ≠ (ι i).high ∧ c ≠ (ι i).low) → bundle allocation c = bundle f c
  high_bound : ∀ i v, v ∈ S → v ≠ (ι i).high → v ≠ (ι i).low →
    (bundle allocation (ι i).high).card ≤ expensiveCount M allocation v (ι i).high + 1
  low_whole : ∀ i v, v ∈ S → v ≠ (ι i).high → v ≠ (ι i).low →
    expensiveCount M allocation v (ι i).low = (bundle allocation (ι i).low).card
  outside_counts : ∀ v, v ∈ S → (∀ i, v ≠ (ι i).high ∧ v ≠ (ι i).low) →
    ∀ c, expensiveCount M allocation v c = expensiveCount M f v c

theorem selected_pair_cycle (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (ι : I ↪ PairIndex M S f) (σ : I ≃ I) (hσ : ∀ i, σ i ≠ i) :
    Nonempty (CycleResult M S f ι) := by
  classical
  have hfill (i : I) :
      ∃ e ∈ bundle f (ι i).high, ¬M.Cheap (ι i).high e :=
    own_expensive_exists M (bad_expensive_positive M (ι i).bad)
  have hlow (i : I) : OwnCheap M f (ι i).low :=
    bad_target_ownCheap M hf.1.1 hs (ι i).members.1 (ι i).bad
  let P : RotatingPairs A E (I) :=
    { high := fun i => (ι i).high
      low := fun i => (ι i).low
      highChore := fun i => Classical.choose (hfill i)
      lowChore := fun i => Classical.choose (hlow i)
      high_injective := (PairIndex.high_injective M hf hs).comp ι.injective
      low_injective := (PairIndex.low_injective M hf hs).comp ι.injective
      cross := fun i j => PairIndex.high_ne_low M hf hs (ι i) (ι j)
      cycle := σ }
  have he (i : I) :
      P.highChore i ∈ bundle f (ι i).high ∧ ¬M.Cheap (ι i).high (P.highChore i) :=
    Classical.choose_spec (hfill i)
  have hd (i : I) :
      P.lowChore i ∈ bundle f (ι i).low ∧ M.Cheap (ι i).low (P.lowChore i) :=
    Classical.choose_spec (hlow i)
  have heOwner (i : I) : f (P.highChore i) = P.high i :=
    (mem_bundle f (ι i).high _).mp (he i).1
  have hdOwner (i : I) : f (P.lowChore i) = P.low i :=
    (mem_bundle f (ι i).low _).mp (hd i).1
  have hdfirst (i : I) : M.Cheap (ι i).high (P.lowChore i) :=
    minimum_bad_target_pure M (hf.energyMinimum M) hs (ι i).members.1 (ι i).members.2 (ι i).bad
      _ (hd i).1 (hd i).2
  have hfillS (i : I) {v : A} (hv : v ∈ S) : ¬M.Cheap v (P.highChore i) := by
    apply filler_not_cheap M hv
    apply separated_expensive_filler M hf.1.1
    simpa only [heOwner] using (he i).2
  have hcheapOutside (i : I) {v : A} (hva : v ≠ (ι i).high) (hvb : v ≠ (ι i).low) :
      ¬M.Cheap v (P.lowChore i) :=
    two_cheap_third M (ι i).bad.1 (hdfirst i) (hd i).2 hva hvb
  have hpred (i : I) : σ.symm i ≠ i := by
    intro h
    apply hσ i
    have h' := congrArg σ h
    simpa only [Equiv.apply_symm_apply] using h'.symm
  let g := P.allocation f
  have hhigh (i : I) : bundle g (ι i).high =
      insert (P.lowChore (σ.symm i)) ((bundle f (ι i).high).erase (P.highChore i)) :=
    P.high_bundle heOwner hdOwner i
  have hlowBundle (i : I) : bundle g (ι i).low =
      insert (P.highChore (σ i)) ((bundle f (ι i).low).erase (P.lowChore i)) :=
    P.low_bundle heOwner hdOwner i
  have hother {c : A} (hc : ∀ i : I, c ≠ (ι i).high ∧ c ≠ (ι i).low) :
      bundle g c = bundle f c := P.other_bundle heOwner hdOwner hc
  have hhighNot (i : I) : P.lowChore (σ.symm i) ∉ bundle f (ι i).high := by
    intro h
    exact (PairIndex.high_ne_low M hf hs (ι i) (ι (σ.symm i)))
      (((mem_bundle f (ι i).high _).mp h).symm.trans (hdOwner _))
  have hlowNot (i : I) : P.highChore (σ i) ∉ bundle f (ι i).low := by
    intro h
    exact (PairIndex.high_ne_low M hf hs (ι (σ i)) (ι i))
      ((heOwner _).symm.trans ((mem_bundle f (ι i).low _).mp h))
  have hsize (c : A) : (bundle g c).card = (bundle f c).card := by
    by_cases hc : ∃ i : I, c = (ι i).high ∨ c = (ι i).low
    · obtain ⟨i, rfl | rfl⟩ := hc
      · exact replacement_card (he i).1 (hhighNot i) (hhigh i)
      · exact replacement_card (hd i).1 (hlowNot i) (hlowBundle i)
    · have hc' : ∀ i : I, c ≠ (ι i).high ∧ c ≠ (ι i).low := by
        intro i
        exact ⟨fun h => hc ⟨i, Or.inl h⟩, fun h => hc ⟨i, Or.inr h⟩⟩
      rw [hother hc']
  have hhighE (i : I) {v : A} (hv : v ∈ S) :
      expensiveCount M g v (ι i).high + 1 = expensiveCount M f v (ι i).high +
        (if M.Cheap v (P.lowChore (σ.symm i)) then 0 else 1) := by
    simpa only [ite_eq_right (hfillS i hv)] using
      replacement_expensive M (he i).1 (hhighNot i) (hhigh i) v
  have hlowE (i : I) {v : A} (hv : v ∈ S) :
      expensiveCount M g v (ι i).low + (if M.Cheap v (P.lowChore i) then 0 else 1) =
        expensiveCount M f v (ι i).low + 1 := by
    simpa only [ite_eq_right (hfillS (σ i) hv)] using
      replacement_expensive M (hd i).1 (hlowNot i) (hlowBundle i) v
  have hforeign (i : I) {v : A} (hv : v = (ι i).high ∨ v = (ι i).low) :
      ¬M.Cheap v (P.lowChore (σ.symm i)) := by
    apply hcheapOutside
    · intro h
      exact hpred i (ι.injective (PairIndex.endpoint_unique M hf hs (Or.inl h) hv))
    · intro h
      exact hpred i (ι.injective (PairIndex.endpoint_unique M hf hs (Or.inr h) hv))
  have hownE (i : I) {v : A} (hv : v = (ι i).high ∨ v = (ι i).low) :
      expensiveCount M g v v = expensiveCount M f (ι i).low (ι i).low + 1 := by
    rcases hv with rfl | rfl
    · have h := hhighE i (ι i).members.1
      rw [ite_eq_right (hforeign i (Or.inl rfl))] at h
      have hc := (minimum_bad_counts M (hf.energyMinimum M) hs (ι i).members.1 (ι i).members.2 (ι i).bad).1
      omega
    · have h := hlowE i (ι i).members.2
      rw [ite_eq_left (hd i).2, add_zero] at h
      exact h
  have hown (i : I) {v : A} (hv : v = (ι i).high ∨ v = (ι i).low) : OwnCheap M g v := by
    rw [ownCheap_iff_count]
    have hsum := cheap_add_expensive M g v v
    rw [hsize, hownE i hv] at hsum
    rcases hv with rfl | rfl
    · have hcount := (minimum_bad_counts M (hf.energyMinimum M) hs (ι i).members.1 (ι i).members.2 (ι i).bad).1
      have hlt := ownCheap_expensive_lt_size M (ι i).bad.2.1
      omega
    · have htwo := optimal_bad_target_two_cheap M hf hs (ι i).members.1 (ι i).members.2 (ι i).bad
      have hold := cheap_add_expensive M f (ι i).low (ι i).low
      omega
  have hunchangedE {v : A} (hv : v ∈ S)
      (hn : ∀ i : I, v ≠ (ι i).high ∧ v ≠ (ι i).low) (c : A) :
      expensiveCount M g v c = expensiveCount M f v c := by
    by_cases hc : ∃ i : I, c = (ι i).high ∨ c = (ι i).low
    · obtain ⟨i, rfl | rfl⟩ := hc
      · have h := hhighE i hv
        rw [ite_eq_right (hcheapOutside (σ.symm i) (hn _).1 (hn _).2)] at h
        omega
      · have h := hlowE i hv
        rw [ite_eq_right (hcheapOutside i (hn i).1 (hn i).2)] at h
        omega
    · have hc' : ∀ i : I, c ≠ (ι i).high ∧ c ≠ (ι i).low := by
        intro i
        exact ⟨fun h => hc ⟨i, Or.inl h⟩, fun h => hc ⟨i, Or.inr h⟩⟩
      rw [expensiveCount, hother hc']
      rfl
  have hstats (i : I) : OrdinaryStats M f g (ι i).high (ι i).low := by
    refine ⟨fun v _ => hsize v, fun v hv => hownE i hv, fun v hv => hown i hv, ?_⟩
    intro v c hv hc hvc
    rcases hv with hv | hv <;> rcases hc with hc | hc <;> subst v <;> subst c
    · exact False.elim (hvc rfl)
    · rw [hownE i (Or.inl rfl)]
      have h := hlowE i (ι i).members.1
      rw [ite_eq_left (hdfirst i), add_zero,
        pure_observer_expensive M hf.1.1 (ι i).members.1
          (minimum_bad_target_pure M (hf.energyMinimum M) hs (ι i).members.1 (ι i).members.2 (ι i).bad)] at h
      omega
    · rw [hownE i (Or.inr rfl)]
      have h := hhighE i (ι i).members.2
      rw [ite_eq_right (hforeign i (Or.inr rfl)),
        pure_observer_expensive M hf.1.1 (ι i).members.2
          (optimal_bad_source_pure M hf hs (ι i).members.1 (ι i).members.2 (ι i).bad)] at h
      have hold := (minimum_bad_counts M (hf.energyMinimum M) hs
        (ι i).members.1 (ι i).members.2 (ι i).bad).1
      omega
    · exact False.elim (hvc rfl)
  refine ⟨⟨g, hsize, hstats, fun c hc => hother hc, ?_, ?_, fun v hv hn c => hunchangedE hv hn c⟩⟩
  · intro i v hv hva hvb
    have h := hhighE i hv
    rw [pure_outside_expensive M hf.1.1 (ι i).bad.1
      (optimal_bad_source_pure M hf hs (ι i).members.1 (ι i).members.2 (ι i).bad) hv hva hvb] at h
    rw [hsize]
    split_ifs at h <;> omega
  · intro i v hv hva hvb
    have h := hlowE i hv
    rw [ite_eq_right (hcheapOutside i hva hvb),
      pure_outside_expensive M hf.1.1 (ι i).bad.1.symm
        (minimum_bad_target_pure M (hf.energyMinimum M) hs (ι i).members.1 (ι i).members.2 (ι i).bad)
        hv hvb hva] at h
    rw [hsize]
    omega

end ResearchMain.Chores

