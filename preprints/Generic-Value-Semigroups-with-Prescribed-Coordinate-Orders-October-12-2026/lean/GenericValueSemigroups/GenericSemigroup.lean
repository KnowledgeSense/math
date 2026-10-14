import GenericValueSemigroups.GreedyJetPolynomials

namespace GenericValueSemigroups

/-- The finite product of all required nonzero integer jet minors. -/
noncomputable def genericJetCondition {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (N : ℕ) : MvPolynomial (JetVariable d N) ℤ :=
  ∏ q : Fin (greedyPrefixCount (weightAt r hr hd) (weightCount r N) N + 1),
    greedyJetPolynomial r hr hd N q.val (Nat.le_of_lt_succ q.isLt)

theorem genericJetCondition_ne_zero {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (N : ℕ) : genericJetCondition r hr hd N ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro q _
  exact greedyJetPolynomial_ne_zero r hr hd N q.val _

theorem genericJetCondition_minors {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (hr : ∀ i, 0 < r i) (hd : 0 < d)
    (hf : ∀ i, PowerSeries.order (f i)=r i)
    (hlead : ∀ i, PowerSeries.coeff (r i) (f i)=1) (N : ℕ)
    (hcondition : jetEvaluation (jetAssignment f r N) (genericJetCondition r hr hd N) ≠ 0)
    (q : ℕ) (hq : q ≤ greedyPrefixCount (weightAt r hr hd) (weightCount r N) N) :
    (greedyMinor (orderedMonomialFamily f r N (orderedWeightEquiv r hr N))
      (weightAt r hr hd) q (hq.trans (greedyPrefixCount_le _ _ _))).det ≠ 0 := by
  rw [← greedyJetPolynomial_eval f r hr hd hf hlead N q hq]
  unfold genericJetCondition at hcondition
  rw [map_prod] at hcondition
  exact Finset.prod_ne_zero_iff.mp hcondition ⟨q, Nat.lt_succ_of_le hq⟩ (Finset.mem_univ _)

theorem generic_polynomial_values_below {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (hr : ∀ i, 0 < r i) (hd : 0 < d)
    (hf : ∀ i, PowerSeries.order (f i)=r i)
    (hlead : ∀ i, PowerSeries.coeff (r i) (f i)=1) (N : ℕ)
    (hcondition : jetEvaluation (jetAssignment f r N) (genericJetCondition r hr hd N) ≠ 0)
    (n : ℕ) (hn : n < N) :
    n ∈ polynomialValues f ↔ n ∈ Set.range (greedy (weightAt r hr hd)) :=
  polynomial_values_below_cutoff f r hr hd hf N (orderedWeightEquiv r hr N)
    (orderedWeightEquiv_weight r hr hd N)
    (genericJetCondition_minors f r hr hd hf hlead N hcondition) n hn

/-- A single finite integer-polynomial condition determines the full formal value semigroup. -/
theorem generic_formal_values_eq {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (hr : ∀ i, 0 < r i) (hd : 0 < d)
    (hf : ∀ i, PowerSeries.order (f i)=r i)
    (hlead : ∀ i, PowerSeries.coeff (r i) (f i)=1) (i : Fin d) (C : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ Set.range (greedy (weightAt r hr hd)))
    (hcondition : jetEvaluation (jetAssignment f r (C+r i))
      (genericJetCondition r hr hd (C+r i)) ≠ 0) :
    formalValues f = Set.range (greedy (weightAt r hr hd)) := by
  have hzero : ∀ i, (f i).constantCoeff = 0 := by
    intro i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    apply PowerSeries.coeff_of_lt_order
    rw [hf]
    exact_mod_cast hr i
  rw [formalValues_eq_polynomialValues f hzero]
  exact polynomial_values_eq_greedy_of_minors f r hr hd hf i C hC
    (orderedWeightEquiv r hr (C+r i)) (orderedWeightEquiv_weight r hr hd (C+r i))
    (genericJetCondition_minors f r hr hd hf hlead (C+r i) hcondition)

theorem exists_family_generic_formal_values {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (i : Fin d) (C : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ Set.range (greedy (weightAt r hr hd))) :
    ∃ f : Fin d → PowerSeries ℂ, (∀ j, PowerSeries.order (f j)=r j) ∧
      (∀ j, PowerSeries.coeff (r j) (f j)=1) ∧
      formalValues f = Set.range (greedy (weightAt r hr hd)) := by
  obtain ⟨a, ha⟩ := exists_jetEvaluation_ne_zero
    (genericJetCondition r hr hd (C+r i)) (genericJetCondition_ne_zero r hr hd (C+r i))
  refine ⟨familyFromJet r a, familyFromJet_order r a, familyFromJet_leading r a, ?_⟩
  apply generic_formal_values_eq _ r hr hd (familyFromJet_order r a)
    (familyFromJet_leading r a) i C hC
  simpa using ha

end GenericValueSemigroups
