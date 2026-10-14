import MainTheorems.Chores.AggregateChores

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

noncomputable def aggregateSplit (M : TwoCheapModel A E) (f : E → A) (a b : A) : E → A :=
  splitAllocation f a b (incidentEdges M {a, b}) (bundle f a \ incidentEdges M {a, b})

theorem aggregate_split_counts (M : TwoCheapModel A E) {a b : A} (hab : a ≠ b)
    (hiso : IsolatedPair M a b) {f : E → A}
    (hf : ∀ e, f e ∈ collapsedAllowed M a b e) (hb : (bundle f b).card = 0)
    {T : ℕ} (hT : (bundle f a).card = T)
    (heven : Even (T - (incidentEdges M {a, b}).card)) :
    (bundle (aggregateSplit M f a b) a).card = T / 2 ∧
      (bundle (aggregateSplit M f a b) b).card = (T + 1) / 2 ∧
      expensiveCount M (aggregateSplit M f a b) a a = (T - (incidentEdges M {a, b}).card) / 2 ∧
      expensiveCount M (aggregateSplit M f a b) b b = (T - (incidentEdges M {a, b}).card) / 2 ∧
      cheapCount M (aggregateSplit M f a b) a a = (incidentEdges M {a, b}).card / 2 ∧
      cheapCount M (aggregateSplit M f a b) b b =
        (incidentEdges M {a, b}).card - (incidentEdges M {a, b}).card / 2 := by
  let D := incidentEdges M {a, b}
  let F := bundle f a \ D
  have hB : bundle f a = D ∪ F := aggregate_partition M hf
  have hD : D ⊆ bundle f a := collapsed_pair_subset M hf
  have hdis : Disjoint D F := Finset.disjoint_sdiff
  have hF : F.card = T - D.card := by
    rw [Finset.card_sdiff_of_subset hD, hT]
  have hsum : D.card + F.card = T := by
    have ht := Finset.card_sdiff_add_card_eq_card hD
    change F.card + D.card = (bundle f a).card at ht
    omega
  have hEF : Even F.card := by rwa [hF]
  have hsplit := split_even_filler hdis hEF
  have hhigh : bundle (aggregateSplit M f a b) a = splitFirst D F :=
    splitAllocation_high hab hB
  have hlow : bundle (aggregateSplit M f a b) b = splitSecond D F :=
    splitAllocation_low hab hB (Finset.card_eq_zero.mp hb)
  have hX : splitFirst D F ⊆ bundle f a := by rw [hB]; exact splitFirst_subset D F
  have hY : splitSecond D F ⊆ bundle f a := by
    rw [hB]
    exact Finset.sdiff_subset
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hhigh, hsplit.2.2.1, hsum]
  · rw [hlow, hsplit.2.2.2, hsum]
  · rw [expensiveCount, hhigh, aggregate_expensive_filter M hiso (Or.inl rfl) hX]
    change (splitFirst D F ∩ F).card = (T - D.card) / 2
    rw [hsplit.1, hF]
  · rw [expensiveCount, hlow, aggregate_expensive_filter M hiso (Or.inr rfl) hY]
    change (splitSecond D F ∩ F).card = (T - D.card) / 2
    rw [hsplit.2.1, hF]
  · rw [cheapCount, hhigh, aggregate_cheap_filter M hiso (Or.inl rfl),
      splitFirst_inter_left hdis, halfSet_card]
  · rw [cheapCount, hlow, aggregate_cheap_filter M hiso (Or.inr rfl),
      splitSecond_inter_left hdis, Finset.card_sdiff_of_subset (halfSet_subset D), halfSet_card]

theorem aggregate_split_other (M : TwoCheapModel A E) {a b c : A} {f : E → A}
    (hca : c ≠ a) (hcb : c ≠ b) : bundle (aggregateSplit M f a b) c = bundle f c :=
  splitAllocation_other hca hcb _ _

theorem isolated_observer_counts (M : TwoCheapModel A E) {a b v w c : A}
    (hiso : IsolatedPair M a b) {f : E → A} (hv : v = a ∨ v = b)
    (hw : w = a ∨ w = b) : expensiveCount M f v c = expensiveCount M f w c := by
  unfold expensiveCount
  congr 1
  ext e
  simp only [Finset.mem_filter, isolated_cheap_iff M hiso hv, isolated_cheap_iff M hiso hw]

end ResearchMain.Chores
