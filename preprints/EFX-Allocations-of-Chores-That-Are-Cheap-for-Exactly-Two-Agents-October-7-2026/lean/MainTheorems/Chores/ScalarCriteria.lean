import MainTheorems.Chores.Reassignment

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

omit [DecidableEq E] in
theorem positive_threshold (M : TwoCheapModel A E) (r : ℝ) {f : E → A} {a : A}
    (hc : OwnCheap M f a) :
    threshold M r f a = (bundle f a).card - 1 + (r - 1) * expensiveCount M f a a := by
  have hne : (bundle f a).Nonempty := by obtain ⟨e, he, _⟩ := hc; exact ⟨e, he⟩
  rw [threshold_eq_counts M r f a hne, ite_eq_left ((ownCheap_iff_count M f a).mp hc)]

omit [DecidableEq E] in
theorem positive_comparison (M : TwoCheapModel A E) {r : ℝ} (hr : 1 ≤ r)
    {f : E → A} {a b : A} (hc : OwnCheap M f a)
    (hsize : (bundle f a).card ≤ (bundle f b).card + 1)
    (hexp : expensiveCount M f a a ≤ expensiveCount M f a b) :
    threshold M r f a ≤ bundleCost M r a (bundle f b) := by
  rw [positive_threshold M r hc, bundleCost_eq_size]
  have hsize' : ((bundle f a).card : ℝ) ≤ (bundle f b).card + 1 := by exact_mod_cast hsize
  have hexp' : (expensiveCount M f a a : ℝ) ≤ expensiveCount M f a b :=
    by exact_mod_cast hexp
  nlinarith

omit [DecidableEq E] in
theorem threshold_eq_of_counts (M : TwoCheapModel A E) (r : ℝ) {f g : E → A} {a : A}
    (hsize : (bundle g a).card = (bundle f a).card)
    (hexp : expensiveCount M g a a = expensiveCount M f a a) :
    threshold M r g a = threshold M r f a := by
  have hf := cheap_add_expensive M f a a
  have hg := cheap_add_expensive M g a a
  have hcheap : cheapCount M g a a = cheapCount M f a a := by omega
  by_cases hne : (bundle f a).Nonempty
  · have hneg : (bundle g a).Nonempty := by
      rw [← Finset.card_pos, hsize]
      exact Finset.card_pos.mpr hne
    rw [threshold_eq_counts M r g a hneg, threshold_eq_counts M r f a hne,
      hcheap, hsize, hexp]
  · have hneg : ¬(bundle g a).Nonempty := by
      rw [← Finset.card_pos, hsize, Finset.card_pos]
      exact hne
    rw [threshold, ite_eq_right hneg, threshold, ite_eq_right hne]

omit [DecidableEq E] in
theorem cost_eq_of_counts (M : TwoCheapModel A E) (r : ℝ) {f g : E → A} {a b : A}
    (hsize : (bundle g b).card = (bundle f b).card)
    (hexp : expensiveCount M g a b = expensiveCount M f a b) :
    bundleCost M r a (bundle g b) = bundleCost M r a (bundle f b) := by
  rw [bundleCost_eq_size, bundleCost_eq_size, hsize, hexp]

omit [DecidableEq E] in
theorem cost_ge_size (M : TwoCheapModel A E) {r : ℝ} (hr : 1 ≤ r) (f : E → A) (a b : A) :
    ((bundle f b).card : ℝ) ≤ bundleCost M r a (bundle f b) := by
  rw [bundleCost_eq_size]
  have he : (0 : ℝ) ≤ expensiveCount M f a b := by positivity
  nlinarith

end ResearchMain.Chores
