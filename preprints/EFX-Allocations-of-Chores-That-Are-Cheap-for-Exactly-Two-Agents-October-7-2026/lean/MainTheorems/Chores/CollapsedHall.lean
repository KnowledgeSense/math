import MainTheorems.Chores.CollapsedPair

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

omit [Fintype A] in
theorem collapsed_confined_empty (M : TwoCheapModel A E) {a b : A} {U : Finset A}
    (ha : a ∉ U) : confinedAllowed (collapsedAllowed M a b) U = ∅ := by
  rw [confinedAllowed, Finset.filter_eq_empty_iff]
  intro e _ he
  exact ha (he (collapsed_contains_high M a b e))

theorem collapsed_confined_incident_disjoint (M : TwoCheapModel A E) {a b : A}
    (hab : a ≠ b) (hiso : IsolatedPair M a b) (U : Finset A) :
    Disjoint (confinedAllowed (collapsedAllowed M a b) U)
      (incidentEdges M ({a, b} ∪ U)ᶜ) := by
  have hd : Disjoint ({a, b} : Finset A) ({a, b} ∪ U)ᶜ := by
    rw [Finset.disjoint_left]
    intro c hc hw
    exact (Finset.mem_compl.mp hw) (Finset.mem_union_left U hc)
  have hpair := isolated_incident_disjoint M hab hiso hd
  rw [Finset.disjoint_left] at hpair ⊢
  intro e he hw
  have hn : e ∉ incidentEdges M {a, b} := fun ht => hpair ht hw
  have hallowed := (Finset.mem_filter.mp he).2
  rw [mem_incidentEdges] at hw
  rcases hw with hw | hw
  · have hU := hallowed (collapsed_endpoint M hn (Or.inl rfl))
    exact (Finset.mem_compl.mp hw) (Finset.mem_union_right _ hU)
  · have hU := hallowed (collapsed_endpoint M hn (Or.inr rfl))
    exact (Finset.mem_compl.mp hw) (Finset.mem_union_right _ hU)

omit [Fintype A] in
theorem collapsed_confined_pair_subset (M : TwoCheapModel A E) {a b : A} {U : Finset A}
    (hU : U \ {a, b} = ∅) :
    confinedAllowed (collapsedAllowed M a b) U ⊆ incidentEdges M {a, b} := by
  have hsub : U ⊆ ({a, b} : Finset A) := Finset.sdiff_eq_empty_iff_subset.mp hU
  intro e he
  by_contra hn
  have hfirst := (Finset.mem_filter.mp he).2 (collapsed_endpoint M hn (Or.inl rfl))
  exact hn ((mem_incidentEdges M {a, b} e).mpr (Or.inl (hsub hfirst)))

theorem collapsed_lower_hall (M : TwoCheapModel A E) {a b : A} (hab : a ≠ b)
    (hiso : IsolatedPair M a b) {μ : ℝ} (hmax : MaxDeficient M μ {a, b})
    {q T : ℕ} (hq : (q : ℝ) ≤ μ)
    (hT : T + q * (Fintype.card A - 2) ≤ Fintype.card E) :
    LowerHall (collapsedAllowed M a b) (collapsedCapacity a b q T) := by
  intro U
  rw [collapsed_capacity_sum q T U]
  by_cases ha : a ∈ U
  · rw [ite_eq_left ha]
    have hi : incidentAllowed (collapsedAllowed M a b) U = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro e
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, collapsed_contains_high M a b e⟩
    rw [hi, Finset.card_univ]
    have hc := pair_outside_card hab U
    have hW : (U \ {a, b}).card ≤ Fintype.card A - 2 := by omega
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left q hW) T).trans hT
  · rw [ite_eq_right ha, zero_add]
    have hd : Disjoint ({a, b} : Finset A) (U \ {a, b}) := Finset.disjoint_sdiff
    have hden := isolated_density M hab hiso hmax hd
    have hcard : (0 : ℝ) ≤ (U \ {a, b}).card := by positivity
    have hl : q * (U \ {a, b}).card ≤ (incidentEdges M (U \ {a, b})).card := by
      have hreal : (q : ℝ) * (U \ {a, b}).card ≤ (incidentEdges M (U \ {a, b})).card :=
        (mul_le_mul_of_nonneg_right hq hcard).trans hden
      exact_mod_cast hreal
    exact hl.trans (Finset.card_le_card (collapsed_outside_incident M hab hiso U))

theorem collapsed_confined_bound (M : TwoCheapModel A E) {a b : A} (hab : a ≠ b)
    (hiso : IsolatedPair M a b) {μ : ℝ} (hmax : MaxDeficient M μ {a, b})
    (hμ : μ * Fintype.card A = Fintype.card E) (U : Finset A) :
    ((confinedAllowed (collapsedAllowed M a b) U).card : ℝ) ≤
      μ * (2 + (U \ {a, b}).card) := by
  have hdis := collapsed_confined_incident_disjoint M hab hiso U
  have hc := Finset.card_le_univ
    (confinedAllowed (collapsedAllowed M a b) U ∪ incidentEdges M ({a, b} ∪ U)ᶜ)
  rw [Finset.card_union_of_disjoint hdis] at hc
  have hcr : ((confinedAllowed (collapsedAllowed M a b) U).card : ℝ) +
      (incidentEdges M ({a, b} ∪ U)ᶜ).card ≤ Fintype.card E := by exact_mod_cast hc
  have hd : Disjoint ({a, b} : Finset A) ({a, b} ∪ U)ᶜ := by
    rw [Finset.disjoint_left]
    intro c hc hw
    exact (Finset.mem_compl.mp hw) (Finset.mem_union_left U hc)
  have hden := isolated_density M hab hiso hmax hd
  have hn : ((({a, b} ∪ U)ᶜ.card : ℕ) : ℝ) + (U \ {a, b}).card + 2 = Fintype.card A := by
    exact_mod_cast pair_outside_card hab U
  have hprod := congrArg (fun x : ℝ => μ * x) hn
  rw [hμ] at hprod
  nlinarith only [hcr, hden, hprod]

theorem collapsed_upper_hall (M : TwoCheapModel A E) {a b : A} (hab : a ≠ b)
    (hiso : IsolatedPair M a b) {μ : ℝ} (hmax : MaxDeficient M μ {a, b})
    (hμ : μ * Fintype.card A = Fintype.card E) {q T : ℕ} (hq : μ ≤ q + 1)
    (hT : 2 * μ < (T : ℝ) + 1 ∨
      μ = q ∧ T + 1 = 2 * q ∧ (incidentEdges M {a, b}).card ≤ T) :
    UpperHall (collapsedAllowed M a b) (collapsedCapacity a b (q + 1) T) := by
  intro U
  rw [collapsed_capacity_sum (q + 1) T U]
  by_cases ha : a ∈ U
  · rw [ite_eq_left ha]
    have hb := collapsed_confined_bound M hab hiso hmax hμ U
    rcases hT with hT | ⟨hμq, hT, hC⟩
    · have hmul : μ * (U \ {a, b}).card ≤ ((q : ℝ) + 1) * (U \ {a, b}).card :=
        mul_le_mul_of_nonneg_right hq (by positivity)
      have ht : ((confinedAllowed (collapsedAllowed M a b) U).card : ℝ) <
          ((T + (q + 1) * (U \ {a, b}).card + 1 : ℕ) : ℝ) := by
        push_cast
        nlinarith only [hb, hmul, hT]
      have ht' : (confinedAllowed (collapsedAllowed M a b) U).card <
          T + (q + 1) * (U \ {a, b}).card + 1 := by exact_mod_cast ht
      omega
    · by_cases hW : U \ {a, b} = ∅
      · rw [hW, Finset.card_empty, Nat.mul_zero, Nat.add_zero]
        exact (Finset.card_le_card (collapsed_confined_pair_subset M hW)).trans hC
      · have hWpos : 0 < (U \ {a, b}).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hW)
        rw [hμq] at hb
        have hb' : (confinedAllowed (collapsedAllowed M a b) U).card ≤
            q * (2 + (U \ {a, b}).card) := by exact_mod_cast hb
        nlinarith only [hb', hWpos, hT]
  · rw [ite_eq_right ha, zero_add, collapsed_confined_empty M ha, Finset.card_empty]
    exact Nat.zero_le _

theorem collapsed_pair_allocation (M : TwoCheapModel A E) {a b : A} (hab : a ≠ b)
    (hiso : IsolatedPair M a b) {μ : ℝ} (hmax : MaxDeficient M μ {a, b})
    (hμ : μ * Fintype.card A = Fintype.card E) {q T : ℕ}
    (hq : (q : ℝ) ≤ μ) (hqu : μ ≤ q + 1)
    (hTl : T + q * (Fintype.card A - 2) ≤ Fintype.card E)
    (hTu : 2 * μ < (T : ℝ) + 1 ∨
      μ = q ∧ T + 1 = 2 * q ∧ (incidentEdges M {a, b}).card ≤ T) :
    ∃ f : E → A, (∀ e, f e ∈ collapsedAllowed M a b e) ∧
      (bundle f a).card = T ∧ (bundle f b).card = 0 ∧
      ∀ c, c ≠ a → c ≠ b → q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1 := by
  have hlu (c : A) : collapsedCapacity a b q T c ≤ collapsedCapacity a b (q + 1) T c := by
    unfold collapsedCapacity
    split_ifs <;> omega
  obtain ⟨f, hf, hc⟩ := bounded_allocation (collapsedAllowed M a b)
    (collapsedCapacity a b q T) (collapsedCapacity a b (q + 1) T) hlu
    (collapsed_lower_hall M hab hiso hmax hq hTl)
    (collapsed_upper_hall M hab hiso hmax hμ hqu hTu)
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · have ht := hc a
    simp [collapsedCapacity] at ht
    omega
  · have ht := hc b
    simp [collapsedCapacity, hab.symm] at ht
    exact Finset.card_eq_zero.mpr ht
  · intro c hca hcb
    simpa only [collapsedCapacity, ite_eq_right hca, ite_eq_right hcb] using hc c

end ResearchMain.Chores
