import MainTheorems.Chores.PairCostBounds

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

theorem aggregate_split_efx (M : TwoCheapModel A E) {a b : A} (hab : a ≠ b)
    (hiso : IsolatedPair M a b) {f : E → A}
    (hf : ∀ e, f e ∈ collapsedAllowed M a b e) (hb : (bundle f b).card = 0)
    {q T : ℕ} (hT : (bundle f a).card = T)
    (heven : Even (T - (incidentEdges M {a, b}).card))
    (hC : 3 ≤ (incidentEdges M {a, b}).card)
    (hTl : 2 * q ≤ T + 1) (hTu : T ≤ 2 * q + 2)
    (hs : ∀ c, c ≠ a → c ≠ b → q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {r : ℝ} (hr : 2 < r) : EFX M r (aggregateSplit M f a b) := by
  let g := aggregateSplit M f a b
  obtain ⟨hsizeA, hsizeB, hEA, hEB, hCA, hCB⟩ :=
    aggregate_split_counts M hab hiso hf hb hT heven
  change (bundle g a).card = T / 2 at hsizeA
  change (bundle g b).card = (T + 1) / 2 at hsizeB
  change expensiveCount M g a a = _ at hEA
  change expensiveCount M g b b = _ at hEB
  change cheapCount M g a a = _ at hCA
  change cheapCount M g b b = _ at hCB
  have hown {v : A} (hv : v = a ∨ v = b) : OwnCheap M g v := by
    rw [ownCheap_iff_count]
    rcases hv with hv | hv <;> subst v
    · rw [hCA]
      omega
    · rw [hCB]
      omega
  have hpairSize {v : A} (hv : v = a ∨ v = b) :
      q ≤ (bundle g v).card + 1 ∧ (bundle g v).card ≤ q + 1 := by
    rcases hv with hv | hv <;> subst v
    · rw [hsizeA]
      omega
    · rw [hsizeB]
      omega
  have hother {c : A} (hca : c ≠ a) (hcb : c ≠ b) : bundle g c = bundle f c :=
    aggregate_split_other M hca hcb
  have hcheapOther {v : A} (hva : v ≠ a) (hvb : v ≠ b) :
      ∀ e ∈ bundle g v, M.Cheap v e := by
    rw [hother hva hvb]
    intro e he
    exact (collapsed_outside_cheap M hf hva he).1
  have hwhole {v c : A} (hv : v = a ∨ v = b) (hca : c ≠ a) (hcb : c ≠ b) :
      expensiveCount M g v c = (bundle g c).card := by
    unfold expensiveCount
    rw [Finset.card_filter_eq_iff]
    intro e he hcheap
    rw [hother hca hcb] at he
    exact (collapsed_outside_cheap M hf hca he).2 ((isolated_cheap_iff M hiso hv e).mp hcheap)
  have hr1 : 1 ≤ r := by linarith
  rw [efx_iff_threshold M hr]
  intro v c hvc
  by_cases hv : v = a ∨ v = b
  · by_cases hc : c = a ∨ c = b
    · apply positive_comparison M hr1 (hown hv)
      · rcases hv with hv | hv <;> rcases hc with hc | hc <;> subst v <;> subst c
        · omega
        · rw [hsizeA, hsizeB]
          omega
        · rw [hsizeA, hsizeB]
          omega
        · omega
      · have heq : expensiveCount M g v c = expensiveCount M g c c :=
          isolated_observer_counts M hiso hv hc
        rw [heq]
        rcases hv with hv | hv <;> rcases hc with hc | hc <;> subst v <;> subst c
        · exact le_rfl
        · rw [hEA, hEB]
        · rw [hEA, hEB]
        · exact le_rfl
    · have hca : c ≠ a := fun ht => hc (Or.inl ht)
      have hcb : c ≠ b := fun ht => hc (Or.inr ht)
      have ht := own_cheap_threshold_bound M (hown hv) hr1
      have hsz : ((bundle g v).card : ℝ) ≤ q + 1 := by exact_mod_cast (hpairSize hv).2
      have hszC : (q : ℝ) ≤ (bundle g c).card := by
        rw [hother hca hcb]
        exact_mod_cast (hs c hca hcb).1
      rw [bundleCost_eq_size, hwhole hv hca hcb]
      nlinarith only [ht, hsz, hszC, hr]
  · have hva : v ≠ a := fun ht => hv (Or.inl ht)
    have hvb : v ≠ b := fun ht => hv (Or.inr ht)
    have hsz : (bundle g v).card ≤ q + 1 := by rw [hother hva hvb]; exact (hs v hva hvb).2
    have ht := all_cheap_threshold_bound M (hcheapOther hva hvb) hsz r
    by_cases hc : c = a ∨ c = b
    · have hcost := outside_cost_ge_pair_cheap M hab hiso hc hva hvb hr1 (f := g)
      have hszC : (q : ℝ) ≤ (bundle g c).card + 1 := by exact_mod_cast (hpairSize hc).1
      have hpos : (1 : ℝ) ≤ cheapCount M g c c := by
        have hn := (ownCheap_iff_count M g c).mp (hown hc)
        exact_mod_cast (show 1 ≤ cheapCount M g c c by omega)
      nlinarith only [ht, hcost, hszC, hpos, hr]
    · have hca : c ≠ a := fun ht => hc (Or.inl ht)
      have hcb : c ≠ b := fun ht => hc (Or.inr ht)
      have hszC : (q : ℝ) ≤ (bundle g c).card := by
        rw [hother hca hcb]
        exact_mod_cast (hs c hca hcb).1
      exact ht.trans (hszC.trans (cost_ge_size M hr1 g v c))

end ResearchMain.Chores
