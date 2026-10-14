import MainTheorems.Chores.PurePairs

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
theorem separated_outside_filler (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {e : E} (he : f e ∉ S) : Filler M S e := by
  have h := hf e
  by_contra hn
  have ht : M.first e ∈ S ∨ M.second e ∈ S := by
    unfold Filler at hn
    tauto
  rw [separatedAllowed, ite_eq_left ht, Finset.mem_inter] at h
  exact he h.2

omit [Fintype E] [DecidableEq E] in
theorem separated_outside_cheap (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {e : E} (he : f e ∉ S) : M.Cheap (f e) e := by
  have hfill := separated_outside_filler M hf he
  have ht : ¬(M.first e ∈ S ∨ M.second e ∈ S) := by
    exact fun h => h.elim hfill.1 hfill.2
  have h := hf e
  rw [separatedAllowed, ite_eq_right ht, Finset.mem_union] at h
  exact h.elim (fun hc => (mem_endpointAllowed M _ e).mp hc) (fun hs => False.elim (he hs))

omit [DecidableEq E] in
theorem separated_outside_own_expensive (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {a : A} (ha : a ∉ S) : expensiveCount M f a a = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have he' := Finset.mem_filter.mp he
  have howner := (mem_bundle f a e).mp he'.1
  have h := separated_outside_cheap M hf (e := e) (by rwa [howner])
  rw [howner] at h
  exact he'.2 h

omit [DecidableEq E] in
theorem separated_outside_target_expensive (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {a b : A} (ha : a ∈ S) (hb : b ∉ S) :
    expensiveCount M f a b = (bundle f b).card := by
  unfold expensiveCount
  rw [Finset.card_filter_eq_iff]
  intro e he
  have howner := (mem_bundle f b e).mp he
  have hfill := separated_outside_filler M hf (e := e) (by rwa [howner])
  exact filler_not_cheap M ha hfill

omit [DecidableEq E] in
theorem threshold_le_balanced (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {f : E → A} {q : ℕ} (hs : ∀ a, q ≤ (bundle f a).card ∧ (bundle f a).card ≤ q + 1)
    (a : A) : threshold M r f a ≤ r * q := by
  by_cases ha : (bundle f a).Nonempty
  · rw [threshold_eq_counts M r f a ha]
    by_cases hc : 0 < cheapCount M f a a
    · rw [ite_eq_left hc]
      have hsum := cheap_add_expensive M f a a
      have hsize := (hs a).2
      have hexp : expensiveCount M f a a ≤ q := by omega
      have hsize' : ((bundle f a).card : ℝ) ≤ q + 1 := by exact_mod_cast hsize
      have hexp' : (expensiveCount M f a a : ℝ) ≤ q := by exact_mod_cast hexp
      nlinarith
    · rw [ite_eq_right hc]
      have hsize : ((bundle f a).card : ℝ) ≤ q + 1 := by exact_mod_cast (hs a).2
      nlinarith
  · rw [threshold, ite_eq_right ha]
    positivity

omit [DecidableEq E] in
theorem separated_outside_threshold (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) (r : ℝ) {q : ℕ}
    (hs : ∀ a, q ≤ (bundle f a).card ∧ (bundle f a).card ≤ q + 1) {a : A} (ha : a ∉ S) :
    threshold M r f a ≤ q := by
  have hexp := separated_outside_own_expensive M hf ha
  by_cases hne : (bundle f a).Nonempty
  · have hown : OwnCheap M f a := by
      obtain ⟨e, he⟩ := hne
      have howner := (mem_bundle f a e).mp he
      have h := separated_outside_cheap M hf (e := e) (by rwa [howner])
      rw [howner] at h
      exact ⟨e, he, h⟩
    rw [threshold_eq_counts M r f a hne, ite_eq_left ((ownCheap_iff_count M f a).mp hown),
      hexp, Nat.cast_zero, mul_zero, add_zero]
    have hsize : ((bundle f a).card : ℝ) ≤ q + 1 := by exact_mod_cast (hs a).2
    linarith
  · rw [threshold, ite_eq_right hne]
    positivity

theorem separated_comparison (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ a, q ≤ (bundle f a).card ∧ (bundle f a).card ≤ q + 1)
    {a b : A} (hab : a ≠ b) (hbad : a ∈ S → b ∈ S → ¬Bad M f a b) :
    threshold M r f a ≤ bundleCost M r a (bundle f b) := by
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · by_cases hne : (bundle f a).Nonempty
      · rw [threshold_eq_counts M r f a hne, bundleCost_eq_size]
        by_cases hc : 0 < cheapCount M f a a
        · rw [ite_eq_left hc]
          have hown := (ownCheap_iff_count M f a).mpr hc
          have hle : expensiveCount M f a a ≤ expensiveCount M f a b := by
            by_contra hn
            have hlt : expensiveCount M f a b < expensiveCount M f a a := by omega
            exact hbad ha hb ⟨hab, hown, hlt⟩
          have hle' : (expensiveCount M f a a : ℝ) ≤ expensiveCount M f a b :=
            by exact_mod_cast hle
          have hsizea : ((bundle f a).card : ℝ) ≤ q + 1 := by exact_mod_cast (hs a).2
          have hsizeb : (q : ℝ) ≤ (bundle f b).card := by exact_mod_cast (hs b).1
          nlinarith
        · rw [ite_eq_right hc]
          have hzero : cheapCount M f a a = 0 := by omega
          have hsum := cheap_add_expensive M f a a
          have hq : (bundle f a).card ≤ (bundle f b).card + 1 := by
            have hqa := (hs a).2
            have hqb := (hs b).1
            omega
          have hq' : ((bundle f a).card : ℝ) ≤ (bundle f b).card + 1 := by exact_mod_cast hq
          by_cases ht : 0 < cheapCount M f a b
          · obtain ⟨d, hd⟩ := Finset.card_pos.mp ht
            have hd' := Finset.mem_filter.mp hd
            have hbound := minimum_exchange_bound M hf ha hb hab hd'.1 hd'.2
            have hge := separated_observer_expensive_ge M hf.1.1 ha (b := b)
            have hle : (bundle f a).card ≤ expensiveCount M f a b + 1 := by omega
            have hle' : ((bundle f a).card : ℝ) ≤ expensiveCount M f a b + 1 :=
              by exact_mod_cast hle
            nlinarith
          · have hz : cheapCount M f a b = 0 := by omega
            have hbsize := cheap_add_expensive M f a b
            have heq : expensiveCount M f a b = (bundle f b).card := by omega
            rw [heq]
            nlinarith
      · rw [threshold, ite_eq_right hne]
        exact bundleCost_nonnegative M hr a _
    · have ht := threshold_le_balanced M hr hs a
      rw [bundleCost_eq_size, separated_outside_target_expensive M hf.1.1 ha hb]
      have hsize : (q : ℝ) ≤ (bundle f b).card := by exact_mod_cast (hs b).1
      nlinarith
  · have ht := separated_outside_threshold M hf.1.1 r hs ha
    rw [bundleCost_eq_size]
    have hsize : (q : ℝ) ≤ (bundle f b).card := by exact_mod_cast (hs b).1
    have hexp : (0 : ℝ) ≤ expensiveCount M f a b := by positivity
    nlinarith

theorem separated_minimum_efx (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ a, q ≤ (bundle f a).card ∧ (bundle f a).card ≤ q + 1)
    (hbad : ∀ a ∈ S, ∀ b ∈ S, ¬Bad M f a b) : EFX M r f := by
  rw [efx_iff_threshold M hr]
  intro a b hab
  exact separated_comparison M hr hf hs hab (hbad a · b ·)

end ResearchMain.Chores
