import MainTheorems.Chores.OptimalAllocation

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

omit [Fintype A] in
theorem exchange_expensive_left (M : TwoCheapModel A E) (f : E → A) {e d : E}
    (hed : e ≠ d) (howners : f e ≠ f d) (a : A) :
    (expensiveCount M (exchange f e d) a (f e) : ℤ) = expensiveCount M f a (f e) -
      (if M.Cheap a e then 0 else 1) + (if M.Cheap a d then 0 else 1) := by
  simpa only [← expensiveCount_eq_sum] using
    exchange_sum_left (fun c => if M.Cheap a c then (0 : ℤ) else 1) f hed howners

omit [Fintype A] in
theorem exchange_expensive_right (M : TwoCheapModel A E) (f : E → A) {e d : E}
    (hed : e ≠ d) (howners : f e ≠ f d) (a : A) :
    (expensiveCount M (exchange f e d) a (f d) : ℤ) = expensiveCount M f a (f d) -
      (if M.Cheap a d then 0 else 1) + (if M.Cheap a e then 0 else 1) := by
  simpa only [← expensiveCount_eq_sum] using
    exchange_sum_right (fun c => if M.Cheap a c then (0 : ℤ) else 1) f hed howners

omit [Fintype A] in
theorem exchange_expensive_other (M : TwoCheapModel A E) (f : E → A) {e d : E} {a b : A}
    (hbe : b ≠ f e) (hbd : b ≠ f d) :
    expensiveCount M (exchange f e d) a b = expensiveCount M f a b := by
  rw [expensiveCount, exchange_bundle_other f hbe hbd]
  rfl

omit [Fintype A] [Fintype E] [DecidableEq E] in
theorem sum_two_changes (S : Finset A) (F G : A → ℕ) {a b : A}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hG : ∀ c ∈ S, c ≠ a → c ≠ b → G c = F c) :
    (∑ c ∈ S, G c) + F a + F b = (∑ c ∈ S, F c) + G a + G b := by
  have hb' : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have htail : (∑ c ∈ (S.erase a).erase b, G c) = ∑ c ∈ (S.erase a).erase b, F c := by
    apply Finset.sum_congr rfl
    intro c hc
    have hc' := Finset.mem_erase.mp hc
    have hc'' := Finset.mem_erase.mp hc'.2
    exact hG c hc''.2 hc''.1 hc'.1
  have hFa := Finset.sum_erase_add (s := S) F ha
  have hFb := Finset.sum_erase_add (s := S.erase a) F hb'
  have hGa := Finset.sum_erase_add (s := S) G ha
  have hGb := Finset.sum_erase_add (s := S.erase a) G hb'
  omega

omit [Fintype A] in
theorem energy_exchange (M : TwoCheapModel A E) {S : Finset A} {f : E → A} {e d : E}
    (hed : e ≠ d) (howners : f e ≠ f d) (heS : f e ∈ S) (hdS : f d ∈ S)
    (he : Filler M S e) (hd₁ : M.Cheap (f e) d) (hd₂ : M.Cheap (f d) d) :
    energy M S (exchange f e d) + 2 * expensiveCount M f (f e) (f e) =
      energy M S f + 2 * expensiveCount M f (f d) (f d) + 2 := by
  have hea := filler_not_cheap M heS he
  have heb := filler_not_cheap M hdS he
  have hla := exchange_expensive_left M f hed howners (f e)
  have hlb := exchange_expensive_right M f hed howners (f d)
  simp only [ite_eq_right hea, ite_eq_right heb, ite_eq_left hd₁, ite_eq_left hd₂] at hla hlb
  have hna : expensiveCount M (exchange f e d) (f e) (f e) + 1 =
      expensiveCount M f (f e) (f e) := by omega
  have hnb : expensiveCount M (exchange f e d) (f d) (f d) =
      expensiveCount M f (f d) (f d) + 1 := by omega
  have hsum := sum_two_changes S (fun a => expensiveCount M f a a ^ 2)
    (fun a => expensiveCount M (exchange f e d) a a ^ 2) heS hdS howners
    (fun a _ hae had => by rw [exchange_expensive_other M f hae had])
  change energy M S (exchange f e d) + expensiveCount M f (f e) (f e) ^ 2 +
      expensiveCount M f (f d) (f d) ^ 2 = energy M S f +
      expensiveCount M (exchange f e d) (f e) (f e) ^ 2 +
      expensiveCount M (exchange f e d) (f d) (f d) ^ 2 at hsum
  nlinarith

omit [Fintype A] in
theorem minimum_exchange_bound (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    (hf : EnergyMinimum M S f₀ f) {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    {d : E} (hdb : d ∈ bundle f b) (hda : M.Cheap a d) :
    expensiveCount M f a a ≤ expensiveCount M f b b + 1 := by
  by_cases hpos : 0 < expensiveCount M f a a
  · obtain ⟨e, hea, hcheap⟩ := own_expensive_exists M hpos
    have heq := (mem_bundle f a e).mp hea
    have hdq := (mem_bundle f b d).mp hdb
    have hed : e ≠ d := by intro h; subst d; exact hab (heq.symm.trans hdq)
    have howners : f e ≠ f d := by simpa only [heq, hdq] using hab
    have hefill := separated_expensive_filler M hf.1.1 (e := e) (by rw [heq]; exact hcheap)
    have hdcheap := separated_owner_cheap M hf.1.1 ha hda
    have heS : f e ∈ S := heq ▸ ha
    have hdS : f d ∈ S := hdq ▸ hb
    have hfeas := feasible_exchange M hf.1 heS hdS hefill (by simpa only [heq] using hda)
    have hmin := hf.2 _ hfeas
    have henergy := energy_exchange M hed howners heS hdS hefill
      (by simpa only [heq] using hda) hdcheap
    rw [heq, hdq] at henergy
    omega
  · omega

omit [Fintype A] in
theorem minimum_bad_counts (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A} {q : ℕ}
    (hf : EnergyMinimum M S f₀ f) (hs : ∀ a, q ≤ (bundle f a).card ∧ (bundle f a).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) :
    expensiveCount M f a a = expensiveCount M f b b + 1 ∧
      expensiveCount M f a b = expensiveCount M f b b := by
  obtain ⟨d, hd, hda⟩ := bad_target_cheap M hbad hs
  have hbnd := minimum_exchange_bound M hf ha hb hbad.1 hd hda
  have hge := separated_observer_expensive_ge M hf.1.1 ha (b := b)
  have hlt := hbad.2.2
  omega

omit [Fintype A] in
theorem minimum_bad_target_pure (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A} {q : ℕ}
    (hf : EnergyMinimum M S f₀ f) (hs : ∀ a, q ≤ (bundle f a).card ∧ (bundle f a).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) : Pure M f b a := by
  have hcounts := (minimum_bad_counts M hf hs ha hb hbad).2
  have hsubset : (bundle f b).filter (fun e => ¬M.Cheap b e) ⊆
      (bundle f b).filter (fun e => ¬M.Cheap a e) := by
    intro e he
    have he' := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨he'.1, ?_⟩
    intro hc
    have ho := separated_owner_cheap M hf.1.1 ha hc
    rw [(mem_bundle f b e).mp he'.1] at ho
    exact he'.2 ho
  have heq : (bundle f b).filter (fun e => ¬M.Cheap b e) =
      (bundle f b).filter (fun e => ¬M.Cheap a e) :=
    Finset.eq_of_subset_of_card_le hsubset (by exact le_of_eq hcounts)
  intro e he hcheap
  by_contra hn
  have hmem : e ∈ (bundle f b).filter (fun e => ¬M.Cheap a e) := Finset.mem_filter.mpr ⟨he, hn⟩
  rw [← heq] at hmem
  exact (Finset.mem_filter.mp hmem).2 hcheap

end ResearchMain.Chores
