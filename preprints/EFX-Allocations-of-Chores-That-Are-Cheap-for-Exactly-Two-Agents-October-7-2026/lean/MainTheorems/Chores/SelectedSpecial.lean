import MainTheorems.Chores.ParallelTransfer
import MainTheorems.Chores.RepairStats

namespace ResearchMain.Chores

variable {A E I : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure SpecialResult (M : TwoCheapModel A E) (S : Finset A) (f : E → A)
    (ι : I ↪ PairIndex M S f) (h : E → A) (q : ℕ) where
  allocation : E → A
  stats : ∀ i, SpecialStats M allocation (ι i).high (ι i).low q
  high_subset : ∀ i, bundle allocation (ι i).high ⊆ bundle f (ι i).high
  other : ∀ c, (∀ i, c ≠ (ι i).high ∧ c ≠ (ι i).low) → bundle allocation c = bundle h c
  whole : ∀ i v c, v ∈ S → v ≠ (ι i).high → v ≠ (ι i).low →
    (c = (ι i).high ∨ c = (ι i).low) → expensiveCount M allocation v c = (bundle allocation c).card

theorem selected_special_moves (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (ι : I ↪ PairIndex M S f)
    (hL : ∀ i, expensiveCount M f (ι i).low (ι i).low + 1 = q)
    (h : E → A)
    (hfixed : ∀ i c, (c = (ι i).high ∨ c = (ι i).low) → bundle h c = bundle f c) :
    Nonempty (SpecialResult M S f ι h q) := by
  classical
  let P : PairedTransfers A E I :=
    { source := fun i => (ι i).high
      target := fun i => (ι i).low
      chore := fun i => Classical.choose (ι i).bad.2.1
      source_injective := (PairIndex.high_injective M hf hs).comp ι.injective
      target_injective := (PairIndex.low_injective M hf hs).comp ι.injective
      cross := fun i j => PairIndex.high_ne_low M hf hs (ι i) (ι j) }
  have he (i : I) : P.chore i ∈ bundle f (ι i).high ∧ M.Cheap (ι i).high (P.chore i) :=
    Classical.choose_spec (ι i).bad.2.1
  have howner (i : I) : h (P.chore i) = P.source i := by
    apply (mem_bundle h (ι i).high (P.chore i)).mp
    rw [hfixed i _ (Or.inl rfl)]
    exact (he i).1
  have hcheapLow (i : I) : M.Cheap (ι i).low (P.chore i) :=
    optimal_bad_source_pure M hf hs (ι i).members.1 (ι i).members.2 (ι i).bad _ (he i).1 (he i).2
  let g := P.allocation h
  have hsource (i : I) : bundle g (ι i).high = (bundle f (ι i).high).erase (P.chore i) := by
    rw [P.source_bundle howner i, hfixed i _ (Or.inl rfl)]
  have htarget (i : I) : bundle g (ι i).low = insert (P.chore i) (bundle f (ι i).low) := by
    rw [P.target_bundle howner i, hfixed i _ (Or.inr rfl)]
  have hn (i : I) : P.chore i ∉ bundle f (ι i).low := by
    intro ht
    exact (ι i).bad.1 (((mem_bundle f (ι i).high _).mp (he i).1).symm.trans
      ((mem_bundle f (ι i).low _).mp ht))
  have hhighE (i : I) (v : A) :
      expensiveCount M g v (ι i).high + (if M.Cheap v (P.chore i) then 0 else 1) =
        expensiveCount M f v (ι i).high := by
    unfold expensiveCount
    rw [hsource, Finset.filter_erase]
    by_cases hc : M.Cheap v (P.chore i)
    · have ht : P.chore i ∉ (bundle f (ι i).high).filter (fun e => ¬M.Cheap v e) := by simp [hc]
      rw [ite_eq_left hc, add_zero, Finset.erase_eq_of_notMem ht]
    · rw [ite_eq_right hc]
      exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨(he i).1, hc⟩)
  have hlowE (i : I) (v : A) : expensiveCount M g v (ι i).low =
      expensiveCount M f v (ι i).low + (if M.Cheap v (P.chore i) then 0 else 1) := by
    unfold expensiveCount
    rw [htarget, Finset.filter_insert]
    by_cases hc : M.Cheap v (P.chore i)
    · simp [hc]
    · simp only [hc, not_false_eq_true, ite_true, ite_false]
      exact Finset.card_insert_of_notMem (fun ht => hn i (Finset.mem_filter.mp ht).1)
  have hstats (i : I) : SpecialStats M g (ι i).high (ι i).low q := by
    have hi := hL i
    obtain ⟨hsa, hsb, _, _⟩ :=
      optimal_special_pair M hf hs (ι i).members.1 (ι i).members.2 (ι i).bad (hL i)
    have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs
      (ι i).members.1 (ι i).members.2 (ι i).bad).1
    have hEa := hhighE i (ι i).high
    have hEb := hlowE i (ι i).low
    rw [ite_eq_left (he i).2, add_zero] at hEa
    rw [ite_eq_left (hcheapLow i), add_zero] at hEb
    refine ⟨?_, ?_, by omega, by omega, ?_, ?_⟩
    · rw [hsource, Finset.card_erase_of_mem (he i).1, hsa]
      omega
    · rw [htarget, Finset.card_insert_of_notMem (hn i), hsb]
    · have ht := hlowE i (ι i).high
      rw [ite_eq_left (he i).2, add_zero,
        pure_observer_expensive M hf.1.1 (ι i).members.1
          (minimum_bad_target_pure M (hf.energyMinimum M) hs
            (ι i).members.1 (ι i).members.2 (ι i).bad)] at ht
      omega
    · have ht := hhighE i (ι i).low
      rw [ite_eq_left (hcheapLow i), add_zero,
        pure_observer_expensive M hf.1.1 (ι i).members.2
          (optimal_bad_source_pure M hf hs (ι i).members.1 (ι i).members.2 (ι i).bad)] at ht
      omega
  refine ⟨⟨g, hstats, ?_, fun c hc => P.other_bundle howner hc, ?_⟩⟩
  · intro i
    rw [hsource]
    exact Finset.erase_subset _ _
  intro i v c hv hva hvb hc
  have hncheap : ¬M.Cheap v (P.chore i) :=
    two_cheap_third M (ι i).bad.1 (he i).2 (hcheapLow i) hva hvb
  rcases hc with hc | hc <;> subst c
  · have ht := hhighE i v
    rw [ite_eq_right hncheap,
      pure_outside_expensive M hf.1.1 (ι i).bad.1
        (optimal_bad_source_pure M hf hs (ι i).members.1 (ι i).members.2 (ι i).bad) hv hva hvb] at ht
    have hsa := (optimal_special_pair M hf hs (ι i).members.1 (ι i).members.2 (ι i).bad (hL i)).1
    rw [(hstats i).high_size]
    omega
  · have ht := hlowE i v
    rw [ite_eq_right hncheap,
      pure_outside_expensive M hf.1.1 (ι i).bad.1.symm
        (minimum_bad_target_pure M (hf.energyMinimum M) hs
          (ι i).members.1 (ι i).members.2 (ι i).bad) hv hvb hva] at ht
    have hsb := (optimal_special_pair M hf hs (ι i).members.1 (ι i).members.2 (ι i).bad (hL i)).2.1
    rw [(hstats i).low_size]
    omega

end ResearchMain.Chores
