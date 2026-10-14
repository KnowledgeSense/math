import MainTheorems.Chores.AggregateEFX
import MainTheorems.Chores.PairParity
import MainTheorems.Chores.InitialAllocation

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

theorem isolated_pair_efx (M : TwoCheapModel A E) {a b : A} (hab : a ≠ b)
    (hiso : IsolatedPair M a b) {μ : ℝ} (hmax : MaxDeficient M μ {a, b})
    (hμ : μ * Fintype.card A = Fintype.card E) (hn : 4 ≤ Fintype.card A)
    (hq : 2 ≤ Fintype.card E / Fintype.card A)
    (hC : 3 ≤ (incidentEdges M {a, b}).card) {r : ℝ} (hr : 2 < r) :
    ∃ g : E → A, EFX M r g := by
  let q := Fintype.card E / Fintype.card A
  obtain ⟨hql, hqu⟩ := average_floor_bounds (by omega : 0 < Fintype.card A) hμ
  have hm : Fintype.card E = q * Fintype.card A + Fintype.card E % Fintype.card A := by
    simpa only [q, Nat.mul_comm, Nat.add_comm] using
      (Nat.mod_add_div (Fintype.card E) (Fintype.card A)).symm
  obtain ⟨T, _, heven, hTl, hTu, hsize⟩ :=
    pair_aggregate_choice hn hq hm hμ hqu (isolated_pair_card_bound M hab hmax)
  obtain ⟨f, hf, ha, hb, hs⟩ :=
    collapsed_pair_allocation M hab hiso hmax hμ hql (le_of_lt hqu) hTl hTu
  have hl : 2 * q ≤ T + 1 := by rcases hsize with h | h <;> omega
  have hu : T ≤ 2 * q + 2 := by rcases hsize with h | h <;> omega
  exact ⟨aggregateSplit M f a b, aggregate_split_efx M hab hiso hf hb ha heven hC hl hu hs hr⟩

omit [Fintype A] in
theorem pair_cheap_card_bound (M : TwoCheapModel A E) {f : E → A} {a b : A}
    (hab : a ≠ b) :
    cheapCount M f a a + cheapCount M f b b ≤ (incidentEdges M {a, b}).card := by
  let C₁ := (bundle f a).filter (M.Cheap a)
  let C₂ := (bundle f b).filter (M.Cheap b)
  have hd : Disjoint C₁ C₂ := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    have ha := (mem_bundle f a e).mp (Finset.mem_filter.mp he₁).1
    have hb := (mem_bundle f b e).mp (Finset.mem_filter.mp he₂).1
    exact hab (ha.symm.trans hb)
  have hsub : C₁ ∪ C₂ ⊆ incidentEdges M {a, b} := by
    intro e he
    rw [mem_incidentEdges]
    rcases Finset.mem_union.mp he with he | he
    · have ht := (Finset.mem_filter.mp he).2
      unfold TwoCheapModel.Cheap at ht
      aesop
    · have ht := (Finset.mem_filter.mp he).2
      unfold TwoCheapModel.Cheap at ht
      aesop
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hc
  exact hc

omit [Fintype A] [DecidableEq E] in
theorem pair_separated_isolated (M : TwoCheapModel A E) {f : E → A} {a b : A}
    (hab : a ≠ b) (hf : Separated M {a, b} f)
    (hp : Pure M f a b) (hq : Pure M f b a) : IsolatedPair M a b := by
  intro e he
  have hi : M.first e ∈ ({a, b} : Finset A) ∧ M.second e ∈ ({a, b} : Finset A) := by
    rcases he with he | he
    · exact pure_vertex_incident_inside M hf (by simp) (by simp) hab hp he
    · exact pure_vertex_incident_inside M hf (by simp) (by simp) hab.symm hq he
  have hd := M.distinct e
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  unfold TwoCheapModel.Cheap
  aesop

theorem isolated_optimal_pair (M : TwoCheapModel A E) {a b : A} {f₀ f : E → A}
    (hf : Optimal M {a, b} f₀ f)
    (hs : ∀ c, Fintype.card E / Fintype.card A ≤ (bundle f c).card ∧
      (bundle f c).card ≤ Fintype.card E / Fintype.card A + 1)
    (hbad : Bad M f a b) (hordinary : expensiveCount M f b b + 1 ≠ Fintype.card E / Fintype.card A)
    {μ : ℝ} (hmax : MaxDeficient M μ {a, b})
    (hμ : μ * Fintype.card A = Fintype.card E) (hH : 2 ≤ ({a, b} : Finset A)ᶜ.card)
    {r : ℝ} (hr : 2 < r) : ∃ g : E → A, EFX M r g := by
  have ha : a ∈ ({a, b} : Finset A) := by simp
  have hb : b ∈ ({a, b} : Finset A) := by simp
  have hab := hbad.1
  have hp := optimal_bad_source_pure M hf hs ha hb hbad
  have hq := minimum_bad_target_pure M (hf.energyMinimum M) hs ha hb hbad
  have hiso := pair_separated_isolated M hab hf.1.1 hp hq
  have hcheapA := (ownCheap_iff_count M f a).mp hbad.2.1
  have hcheapB := optimal_bad_target_two_cheap M hf hs ha hb hbad
  have hcard := pair_cheap_card_bound M hab (f := f)
  have hC : 3 ≤ (incidentEdges M {a, b}).card := by omega
  have hq2 := (optimal_ordinary_pair M hf hs ha hb hbad hordinary).1
  have hn : 4 ≤ Fintype.card A := by
    have ht := Finset.card_add_card_compl ({a, b} : Finset A)
    rw [Finset.card_pair hab] at ht
    omega
  exact isolated_pair_efx M hab hiso hmax hμ hn hq2 hC hr

end ResearchMain.Chores
