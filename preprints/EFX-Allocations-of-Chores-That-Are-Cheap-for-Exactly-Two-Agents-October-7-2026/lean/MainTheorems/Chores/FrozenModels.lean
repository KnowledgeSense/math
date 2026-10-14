import MainTheorems.Chores.EarlyCases

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

def freezeExternal (M : TwoCheapModel A E) (S : Finset A) (f : E → A) (a b : A)
    (hab : a ≠ b) : TwoCheapModel A E where
  first e := if f e ∈ S then M.first e else f e
  second e := if f e ∈ S then M.second e else if f e = a then b else a
  distinct e := by
    by_cases he : f e ∈ S
    · simpa only [ite_eq_left he] using M.distinct e
    · simp only [ite_eq_right he]
      by_cases hea : f e = a
      · simpa [hea] using hab
      · simpa only [ite_eq_right hea] using hea

omit [Fintype E] [DecidableEq E] in
theorem frozen_cheap_inside (M : TwoCheapModel A E) (S : Finset A) (f : E → A) (a b : A)
    (hab : a ≠ b) {e : E} (he : f e ∈ S) (c : A) :
    (freezeExternal M S f a b hab).Cheap c e ↔ M.Cheap c e := by
  simp [TwoCheapModel.Cheap, freezeExternal, he]

omit [Fintype E] [DecidableEq E] in
theorem frozen_filler_inside (M : TwoCheapModel A E) (S : Finset A) (f : E → A) (a b : A)
    (hab : a ≠ b) {e : E} (he : f e ∈ S) :
    Filler (freezeExternal M S f a b hab) S e ↔ Filler M S e := by
  simp [Filler, freezeExternal, he]

omit [Fintype E] [DecidableEq E] in
theorem frozen_outside_filler (M : TwoCheapModel A E) (S : Finset A) (f : E → A)
    {a b : A} (hab : a ≠ b) (ha : a ∉ S) (hb : b ∉ S) {e : E} (he : f e ∉ S) :
    Filler (freezeExternal M S f a b hab) S e := by
  simp only [Filler, freezeExternal, ite_eq_right he]
  split_ifs <;> exact ⟨he, by assumption⟩

omit [Fintype E] [DecidableEq E] in
theorem frozen_initial_separated (M : TwoCheapModel A E) (S : Finset A) (f : E → A)
    {a b : A} (hab : a ≠ b) (ha : a ∉ S) (hb : b ∉ S)
    (hf : ∀ e, f e ∈ S → M.Cheap (f e) e ∨ Filler M S e) :
    Separated (freezeExternal M S f a b hab) S f := by
  let N := freezeExternal M S f a b hab
  intro e
  by_cases he : f e ∈ S
  · rcases hf e he with hc | hc
    · have hcheap : N.Cheap (f e) e := (frozen_cheap_inside M S f a b hab he _).mpr hc
      have ht : N.first e ∈ S ∨ N.second e ∈ S := by
        rcases hcheap with h | h
        · exact Or.inl (h ▸ he)
        · exact Or.inr (h ▸ he)
      rw [separatedAllowed, ite_eq_left ht]
      exact Finset.mem_inter.mpr ⟨(mem_endpointAllowed N _ e).mpr hcheap, he⟩
    · have hfill : Filler N S e := (frozen_filler_inside M S f a b hab he).mpr hc
      have ht : ¬(N.first e ∈ S ∨ N.second e ∈ S) := fun h => h.elim hfill.1 hfill.2
      rw [separatedAllowed, ite_eq_right ht]
      exact Finset.mem_union_right _ he
  · have hfill : Filler N S e := frozen_outside_filler M S f hab ha hb he
    have ht : ¬(N.first e ∈ S ∨ N.second e ∈ S) := fun h => h.elim hfill.1 hfill.2
    rw [separatedAllowed, ite_eq_right ht]
    apply Finset.mem_union_left
    apply (mem_endpointAllowed N _ e).mpr
    exact Or.inl (by simp [N, freezeExternal, he])

omit [DecidableEq E] in
theorem feasible_original_inside (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    (hf : Feasible M S f₀ f) {e : E} (he : f e ∈ S) : f₀ e ∈ S := by
  by_contra hn
  rw [hf.2.2 e hn] at he
  exact hn he

omit [DecidableEq E] in
theorem frozen_cost_eq (M : TwoCheapModel A E) (S : Finset A) (f₀ : E → A) (a b : A)
    (hab : a ≠ b) {f : E → A} (hf : Feasible (freezeExternal M S f₀ a b hab) S f₀ f)
    {d : A} (hd : d ∈ S) (r : ℝ) (c : A) :
    bundleCost (freezeExternal M S f₀ a b hab) r c (bundle f d) =
      bundleCost M r c (bundle f d) := by
  apply Finset.sum_congr rfl
  intro e he
  have ho : f e ∈ S := by rwa [(mem_bundle f d e).mp he]
  have hi := feasible_original_inside _ hf ho
  simp [itemCost, frozen_cheap_inside M S f₀ a b hab hi c]

omit [DecidableEq E] in
theorem frozen_expensive_eq (M : TwoCheapModel A E) (S : Finset A) (f₀ : E → A) (a b : A)
    (hab : a ≠ b) {f : E → A} (hf : Feasible (freezeExternal M S f₀ a b hab) S f₀ f)
    {d : A} (hd : d ∈ S) (c : A) :
    expensiveCount (freezeExternal M S f₀ a b hab) f c d = expensiveCount M f c d := by
  unfold expensiveCount
  congr 1
  ext e
  by_cases he : e ∈ bundle f d
  · have ho : f e ∈ S := by rwa [(mem_bundle f d e).mp he]
    have hi := feasible_original_inside _ hf ho
    simp [he, frozen_cheap_inside M S f₀ a b hab hi c]
  · simp [he]

end ResearchMain.Chores
