import MainTheorems.Chores.Transfer

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

omit [DecidableEq E] in
theorem pure_outside_expensive (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {a b c : A} (hab : a ≠ b) (hp : Pure M f a b)
    (hc : c ∈ S) (hca : c ≠ a) (hcb : c ≠ b) :
    expensiveCount M f c a = (bundle f a).card := by
  unfold expensiveCount
  rw [Finset.card_filter_eq_iff]
  intro e he hcheap
  have hown := separated_owner_cheap M hf hc hcheap
  rw [(mem_bundle f a e).mp he] at hown
  exact (two_cheap_third M hab hown (hp e he hown) hca hcb) hcheap

theorem single_special_pair (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hunique : UniqueBad M S f a b)
    (hL : expensiveCount M f b b + 1 = q) : ∃ g : E → A, EFX M r g := by
  have hbad := hunique.1
  obtain ⟨haSize, hbSize, haCheap, hbCheap⟩ := optimal_special_pair M hf hs ha hb hbad hL
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hbad).1
  have hpA := optimal_bad_source_pure M hf hs ha hb hbad
  have hpB := minimum_bad_target_pure M (hf.energyMinimum M) hs ha hb hbad
  obtain ⟨e, he, heCheap⟩ := hbad.2.1
  have heq := (mem_bundle f a e).mp he
  have heB := hpA e he heCheap
  have howner : f e ≠ b := by simpa only [heq] using hbad.1
  let g := transfer f e b
  have hsep : Separated M S g := transfer_separated M hf.1.1 e hb heB
  have hcardA : (bundle g a).card = q := by
    have h : (bundle g a).card + 1 = q + 1 := by
      simpa only [g, heq, haSize] using transfer_source_card f e howner
    omega
  have hcardB : (bundle g b).card = q + 2 := by
    simpa only [hbSize, Nat.add_assoc] using transfer_target_card f e howner
  have hcardOther {c : A} (hca : c ≠ a) (hcb : c ≠ b) : bundle g c = bundle f c := by
    apply transfer_other_bundle f e
    · rwa [heq]
    · exact hcb
  have hexpA : expensiveCount M g a a = q := by
    have h := transfer_source_expensive M f e howner a
    rw [heq, ite_eq_left heCheap, add_zero, hcounts, hL] at h
    exact h
  have hexpB : expensiveCount M g b b = expensiveCount M f b b := by
    simpa only [ite_eq_left heB, add_zero] using transfer_target_expensive M f e howner b
  have hcheapA : cheapCount M g a a = 0 := by
    have h := cheap_add_expensive M g a a
    rw [hcardA, hexpA] at h
    omega
  have hcheapB : cheapCount M g b b = 3 := by
    have h := cheap_add_expensive M g b b
    rw [hcardB, hexpB] at h
    omega
  have hownB : OwnCheap M g b := by rw [ownCheap_iff_count, hcheapB]; omega
  have hpNewA : Pure M g a b := by
    intro d hd hc
    have hpos := (ownCheap_iff_count M g a).mp ⟨d, hd, hc⟩
    omega
  have hpNewB : Pure M g b a := by
    intro d hd hc
    rw [transfer_target_bundle] at hd
    rcases Finset.mem_insert.mp hd with h | h
    · subst d
      exact heCheap
    · exact hpB d h hc
  have hqpos : 0 < q := by omega
  have hneA : (bundle g a).Nonempty := by rw [← Finset.card_pos, hcardA]; exact hqpos
  have htA : threshold M r g a = r * ((q : ℝ) - 1) := by
    rw [threshold_eq_counts M r g a hneA, hcheapA, ite_eq_right (Nat.lt_irrefl 0), hcardA]
  have htB : threshold M r g b = 2 + r * expensiveCount M f b b := by
    rw [positive_threshold M r hownB, hcardB, hexpB]
    have hL' : (expensiveCount M f b b : ℝ) + 1 = q := by exact_mod_cast hL
    push_cast
    nlinarith
  have hL' : (expensiveCount M f b b : ℝ) + 1 = q := by exact_mod_cast hL
  have htPair {v : A} (hv : v = a ∨ v = b) : threshold M r g v ≤ r * q := by
    rcases hv with rfl | rfl
    · rw [htA]
      nlinarith
    · rw [htB]
      nlinarith
  have hminsize (c : A) : q ≤ (bundle g c).card := by
    by_cases hca : c = a
    · subst c
      rw [hcardA]
    · by_cases hcb : c = b
      · subst c
        rw [hcardB]
        omega
      · rw [hcardOther hca hcb]
        exact (hs c).1
  have hr1 : 1 ≤ r := by linarith
  refine ⟨g, ?_⟩
  rw [efx_iff_threshold M hr]
  intro v c hvc
  by_cases hv : v = a ∨ v = b
  · by_cases hcp : c = a ∨ c = b
    · rcases hv with rfl | rfl <;> rcases hcp with rfl | rfl
      · exact False.elim (hvc rfl)
      · rw [htA, bundleCost_eq_size, pure_observer_expensive M hsep ha hpNewB, hcardB, hexpB]
        push_cast
        nlinarith
      · rw [htB, bundleCost_eq_size, pure_observer_expensive M hsep hb hpNewA, hcardA, hexpA]
        nlinarith
      · exact False.elim (hvc rfl)
    · have hca : c ≠ a := fun h => hcp (Or.inl h)
      have hcb : c ≠ b := fun h => hcp (Or.inr h)
      rw [hcardOther hca hcb, bundleCost_eq_size]
      have hvS : v ∈ S := hv.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
      have hE : q ≤ expensiveCount M f v c := by
        by_cases hcS : c ∈ S
        · rcases hv with rfl | rfl
          · simpa only [hL] using optimal_pair_high_margin M hf hs ha hb hcS hbad hca hcb
          · simpa only [hL] using optimal_pair_low_margin M hf hs ha hb hcS hbad hca hcb
        · rw [separated_outside_target_expensive M hf.1.1 hvS hcS]
          exact (hs c).1
      have hE' : (q : ℝ) ≤ expensiveCount M f v c := by exact_mod_cast hE
      have hsize : (q : ℝ) ≤ (bundle f c).card := by exact_mod_cast (hs c).1
      have ht := htPair hv
      nlinarith
  · have hva : v ≠ a := fun h => hv (Or.inl h)
    have hvb : v ≠ b := fun h => hv (Or.inr h)
    have hth : threshold M r g v = threshold M r f v := by
      apply threshold_eq_of_counts M r
      · rw [hcardOther hva hvb]
      · rw [expensiveCount, hcardOther hva hvb]
        rfl
    rw [hth]
    by_cases hvS : v ∈ S
    · by_cases hcp : c = a ∨ c = b
      · have ht := threshold_le_balanced M hr hs v
        have hewhole : expensiveCount M g v c = (bundle g c).card := by
          rcases hcp with rfl | rfl
          · exact pure_outside_expensive M hsep hbad.1 hpNewA hvS hva hvb
          · exact pure_outside_expensive M hsep hbad.1.symm hpNewB hvS hvb hva
        rw [bundleCost_eq_size, hewhole]
        have hsize : (q : ℝ) ≤ (bundle g c).card := by exact_mod_cast hminsize c
        nlinarith
      · have hca : c ≠ a := fun h => hcp (Or.inl h)
        have hcb : c ≠ b := fun h => hcp (Or.inr h)
        rw [hcardOther hca hcb]
        apply separated_comparison M hr (hf.energyMinimum M) hs hvc
        intro hv' hc' hnew
        exact hva (hunique.2 v hv' c hc' hnew).1
    · have ht := separated_outside_threshold M hf.1.1 r hs hvS
      have hcge := cost_ge_size M hr1 g v c
      have hsize : (q : ℝ) ≤ (bundle g c).card := by exact_mod_cast hminsize c
      linarith

end ResearchMain.Chores
