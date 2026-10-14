import MainTheorems.Chores.FrozenModels

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A]

theorem feasible_outside_bundle (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    (hf : Feasible M S f₀ f) {v : A} (hv : v ∉ S) : bundle f v = bundle f₀ v := by
  have hsub : bundle f₀ v ⊆ bundle f v := by
    intro e he
    rw [mem_bundle] at he ⊢
    rw [hf.2.2 e (by rwa [he]), he]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hf.2.1 v])).symm

theorem feasible_inside_iff (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    (hf : Feasible M S f₀ f) (e : E) : f e ∈ S ↔ f₀ e ∈ S := by
  constructor
  · exact feasible_original_inside M hf
  · intro he
    by_contra hn
    have ht : e ∈ bundle f (f e) := (mem_bundle f (f e) e).mpr rfl
    rw [feasible_outside_bundle M hf hn] at ht
    have hown := (mem_bundle f₀ (f e) e).mp ht
    exact hn (hown ▸ he)

theorem frozen_cheap_count_eq (M : TwoCheapModel A E) (S : Finset A) (f₀ : E → A) (a b : A)
    (hab : a ≠ b) {f : E → A} (hf : Feasible (freezeExternal M S f₀ a b hab) S f₀ f)
    {d : A} (hd : d ∈ S) (c : A) :
    cheapCount (freezeExternal M S f₀ a b hab) f c d = cheapCount M f c d := by
  have h₁ := cheap_add_expensive (freezeExternal M S f₀ a b hab) f c d
  have h₂ := cheap_add_expensive M f c d
  rw [frozen_expensive_eq M S f₀ a b hab hf hd c] at h₁
  omega

theorem frozen_own_cheap_iff (M : TwoCheapModel A E) (S : Finset A) (f₀ : E → A) (a b : A)
    (hab : a ≠ b) {f : E → A} (hf : Feasible (freezeExternal M S f₀ a b hab) S f₀ f)
    {d : A} (hd : d ∈ S) : OwnCheap (freezeExternal M S f₀ a b hab) f d ↔ OwnCheap M f d := by
  rw [ownCheap_iff_count, ownCheap_iff_count, frozen_cheap_count_eq M S f₀ a b hab hf hd d]

theorem frozen_threshold_eq (M : TwoCheapModel A E) (S : Finset A) (f₀ : E → A) (a b : A)
    (hab : a ≠ b) {f : E → A} (hf : Feasible (freezeExternal M S f₀ a b hab) S f₀ f)
    {d : A} (hd : d ∈ S) (r : ℝ) :
    threshold (freezeExternal M S f₀ a b hab) r f d = threshold M r f d := by
  unfold threshold
  rw [frozen_cost_eq M S f₀ a b hab hf hd r d]
  simp only [frozen_own_cheap_iff M S f₀ a b hab hf hd]

theorem frozen_bad_iff (M : TwoCheapModel A E) (S : Finset A) (f₀ : E → A) (a b : A)
    (hab : a ≠ b) {f : E → A} (hf : Feasible (freezeExternal M S f₀ a b hab) S f₀ f)
    {v d : A} (hv : v ∈ S) (hd : d ∈ S) :
    Bad (freezeExternal M S f₀ a b hab) f v d ↔ Bad M f v d := by
  unfold Bad
  rw [frozen_own_cheap_iff M S f₀ a b hab hf hv,
    frozen_expensive_eq M S f₀ a b hab hf hd v, frozen_expensive_eq M S f₀ a b hab hf hv v]

theorem frozen_pure_iff (M : TwoCheapModel A E) (S : Finset A) (f₀ : E → A) (a b : A)
    (hab : a ≠ b) {f : E → A} (hf : Feasible (freezeExternal M S f₀ a b hab) S f₀ f)
    {v : A} (hv : v ∈ S) (d : A) :
    Pure (freezeExternal M S f₀ a b hab) f v d ↔ Pure M f v d := by
  have he {e : E} (he : e ∈ bundle f v) : f₀ e ∈ S := by
    apply feasible_original_inside _ hf
    rwa [(mem_bundle f v e).mp he]
  unfold Pure
  constructor <;> intro hp e heb hc
  · exact (frozen_cheap_inside M S f₀ a b hab (he heb) d).mp
      (hp e heb ((frozen_cheap_inside M S f₀ a b hab (he heb) v).mpr hc))
  · exact (frozen_cheap_inside M S f₀ a b hab (he heb) d).mpr
      (hp e heb ((frozen_cheap_inside M S f₀ a b hab (he heb) v).mp hc))

end ResearchMain.Chores
