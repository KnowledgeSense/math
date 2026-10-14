import MainTheorems.Chores.SeparatedEFX

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

theorem optimal_pair_no_reverse (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) : ¬Bad M f b a := by
  have hp := optimal_bad_source_pure M hf hs ha hb hbad
  have heq := pure_observer_expensive M hf.1.1 hb hp
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hbad).1
  intro hreverse
  have hlt := hreverse.2.2
  rw [heq] at hlt
  omega

theorem optimal_pair_low_no_outgoing (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b c : A} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hbad : Bad M f a b) :
    ¬Bad M f b c := by
  intro hnew
  have hp := minimum_bad_target_pure M (hf.energyMinimum M) hs ha hb hbad
  have hq := optimal_bad_source_pure M hf hs hb hc hnew
  have hown := bad_target_ownCheap M hf.1.1 hs ha hbad
  have heq := pure_unique M hown hbad.1.symm hnew.1 hp hq
  subst c
  exact optimal_pair_no_reverse M hf hs ha hb hbad hnew

theorem optimal_pair_high_no_incoming (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b c : A} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hbad : Bad M f a b) :
    ¬Bad M f c a := by
  intro hnew
  have hp := optimal_bad_source_pure M hf hs ha hb hbad
  have hq := minimum_bad_target_pure M (hf.energyMinimum M) hs hc ha hnew
  have heq := pure_unique M hbad.2.1 hbad.1 hnew.1.symm hp hq
  subst c
  exact optimal_pair_no_reverse M hf hs ha hb hbad hnew

theorem optimal_pair_low_incoming_unique (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b c : A} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hbad : Bad M f a b)
    (hnew : Bad M f c b) : c = a := by
  have hp := minimum_bad_target_pure M (hf.energyMinimum M) hs ha hb hbad
  have hq := minimum_bad_target_pure M (hf.energyMinimum M) hs hc hb hnew
  have hown := bad_target_ownCheap M hf.1.1 hs ha hbad
  exact (pure_unique M hown hbad.1.symm hnew.1.symm hp hq).symm

omit [DecidableEq E] in
theorem pure_vertex_incident_inside (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hp : Pure M f a b) {e : E} (hc : M.Cheap a e) :
    M.first e ∈ S ∧ M.second e ∈ S := by
  have ht : M.first e ∈ S ∨ M.second e ∈ S := by
    rcases hc with h | h
    · exact Or.inl (h ▸ ha)
    · exact Or.inr (h ▸ ha)
  have hf' := hf e
  rw [separatedAllowed, ite_eq_left ht, Finset.mem_inter, mem_endpointAllowed] at hf'
  by_contra hn
  have howner : f e = a := by
    unfold TwoCheapModel.Cheap at hc hf'
    aesop
  have hea : e ∈ bundle f a := (mem_bundle f a e).mpr howner
  have hcb := hp e hea hc
  unfold TwoCheapModel.Cheap at hc hcb
  aesop

theorem optimal_bad_expensive_bound (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) :
    expensiveCount M f b b < q := by
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hbad).1
  have hlt := ownCheap_expensive_lt_size M hbad.2.1
  have hsize := (hs a).2
  omega

theorem optimal_special_pair (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b)
    (hL : expensiveCount M f b b + 1 = q) :
    (bundle f a).card = q + 1 ∧ (bundle f b).card = q + 1 ∧
      cheapCount M f a a = 1 ∧ cheapCount M f b b = 2 := by
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hbad).1
  have hlt := ownCheap_expensive_lt_size M hbad.2.1
  have htwo := optimal_bad_target_two_cheap M hf hs ha hb hbad
  have hsum₁ := cheap_add_expensive M f a a
  have hsum₂ := cheap_add_expensive M f b b
  have hsa := (hs a).2
  have hsb := (hs b).2
  omega

theorem optimal_ordinary_pair (M : TwoCheapModel A E)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b)
    (hL : expensiveCount M f b b + 1 ≠ q) :
    2 ≤ q ∧ expensiveCount M f b b + 2 ≤ q := by
  have hlt := optimal_bad_expensive_bound M hf hs ha hb hbad
  omega

end ResearchMain.Chores
