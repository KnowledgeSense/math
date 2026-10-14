import MainTheorems.Chores.BadPairs
import MainTheorems.Chores.SpecialPair

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A]

structure OrdinaryStats (M : TwoCheapModel A E) (f g : E → A) (a b : A) where
  size : ∀ v, v = a ∨ v = b → (bundle g v).card = (bundle f v).card
  expensive : ∀ v, v = a ∨ v = b → expensiveCount M g v v = expensiveCount M f b b + 1
  cheap : ∀ v, v = a ∨ v = b → OwnCheap M g v
  comparison_expensive : ∀ v c, (v = a ∨ v = b) → (c = a ∨ c = b) → v ≠ c →
    expensiveCount M g v v ≤ expensiveCount M g v c

structure SpecialStats (M : TwoCheapModel A E) (g : E → A) (a b : A) (q : ℕ) where
  high_size : (bundle g a).card = q
  low_size : (bundle g b).card = q + 2
  high_expensive : expensiveCount M g a a = q
  low_expensive : expensiveCount M g b b + 1 = q
  high_to_low : expensiveCount M g a b = expensiveCount M g b b
  low_to_high : expensiveCount M g b a = q

namespace OrdinaryStats

theorem of_counts {M : TwoCheapModel A E} {f g h : E → A} {a b : A}
    (B : OrdinaryStats M f g a b)
    (hs : ∀ v, v = a ∨ v = b → (bundle h v).card = (bundle g v).card)
    (he : ∀ v c, (v = a ∨ v = b) → (c = a ∨ c = b) →
      expensiveCount M h v c = expensiveCount M g v c) : OrdinaryStats M f h a b := by
  have hc {v : A} (hv : v = a ∨ v = b) : cheapCount M h v v = cheapCount M g v v := by
    have h₁ := cheap_add_expensive M h v v
    have h₂ := cheap_add_expensive M g v v
    rw [hs v hv, he v v hv hv] at h₁
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hs v hv]
    exact B.size v hv
  · intro v hv
    rw [he v v hv hv]
    exact B.expensive v hv
  · intro v hv
    rw [ownCheap_iff_count, hc hv]
    exact (ownCheap_iff_count M g v).mp (B.cheap v hv)
  · intro v c hv hv' hvc
    rw [he v v hv hv, he v c hv hv']
    exact B.comparison_expensive v c hv hv' hvc

theorem of_pair_bundles {M : TwoCheapModel A E} {f g h : E → A} {a b : A}
    (B : OrdinaryStats M f g a b)
    (hh : ∀ v, v = a ∨ v = b → bundle h v = bundle g v) : OrdinaryStats M f h a b := by
  have hex (v c : A) (hc : c = a ∨ c = b) : expensiveCount M h v c = expensiveCount M g v c := by
    rw [expensiveCount, hh c hc]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hh v hv]
    exact B.size v hv
  · intro v hv
    rw [hex v v hv]
    exact B.expensive v hv
  · intro v hv
    unfold OwnCheap
    rw [hh v hv]
    exact B.cheap v hv
  · intro v c hv hc hvc
    rw [hex v v hv, hex v c hc]
    exact B.comparison_expensive v c hv hc hvc

theorem threshold_bound {M : TwoCheapModel A E} {f g : E → A} {a b : A} {q : ℕ}
    (B : OrdinaryStats M f g a b) {r : ℝ} (hr : 2 < r)
    (hs : ∀ c, (bundle f c).card ≤ q + 1)
    (hL : expensiveCount M f b b + 2 ≤ q) {v : A} (hv : v = a ∨ v = b) :
    threshold M r g v ≤ r * ((q : ℝ) - 1) + 1 := by
  rw [positive_threshold M r (B.cheap v hv), B.size v hv, B.expensive v hv]
  have hsz : ((bundle f v).card : ℝ) ≤ q + 1 := by exact_mod_cast hs v
  have hex : (expensiveCount M f b b : ℝ) + 2 ≤ q := by exact_mod_cast hL
  push_cast
  nlinarith only [hsz, hex, hr]

end OrdinaryStats

namespace SpecialStats

theorem of_counts {M : TwoCheapModel A E} {g h : E → A} {a b : A} {q : ℕ}
    (B : SpecialStats M g a b q)
    (hs : ∀ v, v = a ∨ v = b → (bundle h v).card = (bundle g v).card)
    (he : ∀ v c, (v = a ∨ v = b) → (c = a ∨ c = b) →
      expensiveCount M h v c = expensiveCount M g v c) : SpecialStats M h a b q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs a (Or.inl rfl)]
    exact B.high_size
  · rw [hs b (Or.inr rfl)]
    exact B.low_size
  · rw [he a a (Or.inl rfl) (Or.inl rfl)]
    exact B.high_expensive
  · rw [he b b (Or.inr rfl) (Or.inr rfl)]
    exact B.low_expensive
  · rw [he a b (Or.inl rfl) (Or.inr rfl), he b b (Or.inr rfl) (Or.inr rfl)]
    exact B.high_to_low
  · rw [he b a (Or.inr rfl) (Or.inl rfl)]
    exact B.low_to_high

theorem high_cheap {M : TwoCheapModel A E} {g : E → A} {a b : A} {q : ℕ}
    (B : SpecialStats M g a b q) : cheapCount M g a a = 0 := by
  have ht := cheap_add_expensive M g a a
  rw [B.high_size, B.high_expensive] at ht
  omega

theorem low_cheap {M : TwoCheapModel A E} {g : E → A} {a b : A} {q : ℕ}
    (B : SpecialStats M g a b q) : OwnCheap M g b := by
  have ht := cheap_add_expensive M g b b
  rw [B.low_size] at ht
  rw [ownCheap_iff_count]
  have he := B.low_expensive
  omega

theorem high_threshold {M : TwoCheapModel A E} {g : E → A} {a b : A} {q : ℕ}
    (B : SpecialStats M g a b q) (r : ℝ) (hq : 0 < q) :
    threshold M r g a = r * ((q : ℝ) - 1) := by
  rw [threshold_eq_counts M r g a (by rw [← Finset.card_pos, B.high_size]; exact hq),
    B.high_cheap, ite_eq_right (Nat.lt_irrefl 0), B.high_size]

theorem low_threshold {M : TwoCheapModel A E} {g : E → A} {a b : A} {q : ℕ}
    (B : SpecialStats M g a b q) (r : ℝ) :
    threshold M r g b = 2 + r * ((q : ℝ) - 1) := by
  rw [positive_threshold M r B.low_cheap, B.low_size]
  have he : (expensiveCount M g b b : ℝ) + 1 = q := by exact_mod_cast B.low_expensive
  push_cast
  have ht : (expensiveCount M g b b : ℝ) = q - 1 := by linarith only [he]
  rw [ht]
  ring

theorem threshold_bound {M : TwoCheapModel A E} {g : E → A} {a b : A} {q : ℕ}
    (B : SpecialStats M g a b q) {r : ℝ} (hr : 2 < r)
    {v : A} (hv : v = a ∨ v = b) : threshold M r g v ≤ r * q := by
  have hq : 0 < q := by have := B.low_expensive; omega
  rcases hv with hv | hv <;> subst v
  · rw [B.high_threshold r hq]
    nlinarith only [hr]
  · rw [B.low_threshold]
    nlinarith only [hr]

theorem mutual_comparison {M : TwoCheapModel A E} {g : E → A} {a b : A} {q : ℕ}
    (B : SpecialStats M g a b q) {r : ℝ} (hr : 2 < r)
    {v c : A} (hv : v = a ∨ v = b) (hc : c = a ∨ c = b) (hvc : v ≠ c) :
    threshold M r g v ≤ bundleCost M r v (bundle g c) := by
  have hq : 0 < q := by have := B.low_expensive; omega
  rcases hv with hv | hv <;> rcases hc with hc | hc <;> subst v <;> subst c
  · exact False.elim (hvc rfl)
  · rw [B.high_threshold r hq, bundleCost_eq_size, B.low_size, B.high_to_low]
    have he : (expensiveCount M g b b : ℝ) + 1 = q := by exact_mod_cast B.low_expensive
    push_cast
    nlinarith only [he, hr]
  · rw [B.low_threshold, bundleCost_eq_size, B.high_size, B.low_to_high]
    nlinarith only [hr]
  · exact False.elim (hvc rfl)

end SpecialStats

end ResearchMain.Chores
