import MainTheorems.Chores.SpecialPair

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A]

theorem positive_threshold_cost (M : TwoCheapModel A E) (r : ℝ) {f : E → A} {a : A}
    (h : OwnCheap M f a) : threshold M r f a = bundleCost M r a (bundle f a) - 1 := by
  have hne : (bundle f a).Nonempty := by obtain ⟨e, he, _⟩ := h; exact ⟨e, he⟩
  rw [threshold, ite_eq_left hne, ite_eq_left h]

theorem pure_observer_cost (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {a b : A} (ha : a ∈ S) (hp : Pure M f b a) (r : ℝ) :
    bundleCost M r a (bundle f b) = bundleCost M r b (bundle f b) := by
  rw [bundleCost_eq_size, bundleCost_eq_size, pure_observer_expensive M hf ha hp]

theorem pure_outside_cost (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {a b c : A} (hab : a ≠ b) (hp : Pure M f a b)
    (hc : c ∈ S) (hca : c ≠ a) (hcb : c ≠ b) (r : ℝ) :
    bundleCost M r c (bundle f a) = r * (bundle f a).card := by
  rw [bundleCost_eq_size, pure_outside_expensive M hf hab hp hc hca hcb]
  ring

end ResearchMain.Chores
