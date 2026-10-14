import MainTheorems.Chores.SelectedCycle
import MainTheorems.Chores.SelectedSpecial
import MainTheorems.Chores.RepairEFX
import MainTheorems.Chores.FiniteRotation

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

abbrev OrdinaryIndex (M : TwoCheapModel A E) (S : Finset A) (f : E → A) (q : ℕ) :=
  {i : PairIndex M S f // expensiveCount M f i.low i.low + 1 ≠ q}

abbrev SpecialIndex (M : TwoCheapModel A E) (S : Finset A) (f : E → A) (q : ℕ) :=
  {i : PairIndex M S f // expensiveCount M f i.low i.low + 1 = q}

theorem multiple_ordinary_pairs (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hn : 2 ≤ Fintype.card (OrdinaryIndex M S f q)) : ∃ g : E → A, EFX M r g := by
  classical
  let O := OrdinaryIndex M S f q
  let J := SpecialIndex M S f q
  let ι : O ↪ PairIndex M S f := ⟨Subtype.val, Subtype.val_injective⟩
  let κ : J ↪ PairIndex M S f := ⟨Subtype.val, Subtype.val_injective⟩
  have hdis (i : O) (j : J) : ι i ≠ κ j := by
    intro ht
    exact i.property (by change expensiveCount M f (ι i).low (ι i).low + 1 = q; rw [ht]; exact j.property)
  have hnotSpecial (i : O) {v : A} (hv : v = (ι i).high ∨ v = (ι i).low) :
      ∀ j : J, v ≠ (κ j).high ∧ v ≠ (κ j).low := by
    intro j
    exact ⟨fun ht => hdis i j (PairIndex.endpoint_unique M hf hs hv (Or.inl ht)),
      fun ht => hdis i j (PairIndex.endpoint_unique M hf hs hv (Or.inr ht))⟩
  have hnotOrdinary (j : J) {v : A} (hv : v = (κ j).high ∨ v = (κ j).low) :
      ∀ i : O, v ≠ (ι i).high ∧ v ≠ (ι i).low := by
    intro i
    exact ⟨fun ht => hdis i j (PairIndex.endpoint_unique M hf hs (Or.inl ht) hv),
      fun ht => hdis i j (PairIndex.endpoint_unique M hf hs (Or.inr ht) hv)⟩
  obtain ⟨σ, hσ⟩ := exists_fixed_point_free_permutation O hn
  obtain ⟨R⟩ := selected_pair_cycle M hf hs ι σ hσ
  obtain ⟨B⟩ := selected_special_moves M hf hs κ (fun j => j.property) R.allocation
    (fun j c hc => R.other c (hnotOrdinary j hc))
  have hordBundle (i : O) {c : A} (hc : c = (ι i).high ∨ c = (ι i).low) :
      bundle B.allocation c = bundle R.allocation c := B.other c (hnotSpecial i hc)
  have hordE (i : O) (v : A) {c : A} (hc : c = (ι i).high ∨ c = (ι i).low) :
      expensiveCount M B.allocation v c = expensiveCount M R.allocation v c := by
    rw [expensiveCount, hordBundle i hc]
    rfl
  have hpairOutside {i j : PairIndex M S f} (hij : i ≠ j) {v : A}
      (hv : v = i.high ∨ v = i.low) : v ≠ j.high ∧ v ≠ j.low :=
    ⟨fun ht => hij (PairIndex.endpoint_unique M hf hs hv (Or.inl ht)),
      fun ht => hij (PairIndex.endpoint_unique M hf hs hv (Or.inr ht))⟩
  have hwholeOriginal {i : PairIndex M S f} {v c : A} (hv : v ∈ S)
      (hvn : v ≠ i.high ∧ v ≠ i.low) (hc : c = i.high ∨ c = i.low) :
      expensiveCount M f v c = (bundle f c).card := by
    rcases hc with hc | hc <;> subst c
    · exact pure_outside_expensive M hf.1.1 i.bad.1
        (optimal_bad_source_pure M hf hs i.members.1 i.members.2 i.bad) hv hvn.1 hvn.2
    · exact pure_outside_expensive M hf.1.1 i.bad.1.symm
        (minimum_bad_target_pure M (hf.energyMinimum M) hs i.members.1 i.members.2 i.bad) hv hvn.2 hvn.1
  refine ⟨B.allocation, repaired_pairs_efx M hr hf hs ?_ ?_ ?_ ?_ ?_⟩
  · intro i hi
    let j : O := ⟨i, hi⟩
    exact (R.stats j).of_pair_bundles (fun v hv => hordBundle j hv)
  · intro i hi
    exact B.stats ⟨i, hi⟩
  · intro v hv
    rw [B.other v (fun j => hv (κ j)), R.other v (fun i => hv (ι i))]
  · intro i j hij v c hv hc
    have hvS : v ∈ S := hv.elim (fun ht => ht ▸ i.members.1) (fun ht => ht ▸ i.members.2)
    have hvj := hpairOutside hij hv
    by_cases hj : expensiveCount M f j.low j.low + 1 = q
    · let k : J := ⟨j, hj⟩
      have hwhole := B.whole k v c hvS hvj.1 hvj.2 hc
      have hsz : q ≤ (bundle B.allocation c).card := by
        have H := B.stats k
        rcases hc with hc | hc <;> subst c
        · have ht : (bundle B.allocation j.high).card = q := H.high_size
          rw [ht]
        · have ht : (bundle B.allocation j.low).card = q + 2 := H.low_size
          rw [ht]
          omega
      rw [hwhole]
      exact ⟨fun _ => hsz, fun _ => by omega⟩
    · let k : O := ⟨j, hj⟩
      rw [hordE k v hc]
      constructor
      · intro hi
        let l : J := ⟨i, hi⟩
        rw [R.outside_counts v hvS (hnotOrdinary l hv) c, hwholeOriginal hvS hvj hc]
        exact (hs c).1
      · intro _
        have hsz : q ≤ (bundle R.allocation c).card := by rw [R.size c]; exact (hs c).1
        rcases hc with hc | hc <;> subst c
        · exact hsz.trans (R.high_bound k v hvS hvj.1 hvj.2)
        · have ht : expensiveCount M R.allocation v j.low = (bundle R.allocation j.low).card :=
            R.low_whole k v hvS hvj.1 hvj.2
          rw [ht]
          omega
  · intro v hvS hvn i c hc
    constructor
    · intro hi
      exact B.whole ⟨i, hi⟩ v c hvS (hvn i).1 (hvn i).2 hc
    · intro hi
      rw [hordE ⟨i, hi⟩ v hc]
      exact R.outside_counts v hvS (fun j => hvn (ι j)) c

end ResearchMain.Chores
