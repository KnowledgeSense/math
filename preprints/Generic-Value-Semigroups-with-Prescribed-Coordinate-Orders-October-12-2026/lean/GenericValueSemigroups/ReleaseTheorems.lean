import GenericValueSemigroups.MainTheorems
import GenericValueSemigroups.NormalizedGerms

namespace GenericValueSemigroups

/-- The release's generic theorem, including the exact normalized formal family and genuine
convergent analytic functions, at the actual conductor plus minimum coordinate order. -/
theorem release_generic_value_theorem {d : ℕ} (hd : 2 ≤ d) (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) :
    ∃ (C : ℕ) (i : Fin d) (P : MvPolynomial (JetVariable d (C+r i)) ℤ),
      (∀ j, r i ≤ r j) ∧ P ≠ 0 ∧
      (∀ N, (∀ n, N ≤ n → n ∈ Set.range (greedy (weightAt r hr (by omega)))) ↔ C ≤ N) ∧
      (∀ a : Fin d → ℕ → ℂ,
        jetEvaluation (fun v => a v.1 (v.2.val+1)) P ≠ 0 →
        formalValues (normalizedFamily r a)=Set.range (greedy (weightAt r hr (by omega)))) ∧
      (∀ F : ℂ → Fin d → ℂ,
        (∀ j, AnalyticAt ℂ (fun t => F t j) 0) →
        (∀ j, analyticOrderAt (fun t => F t j) 0=r j) →
        (∀ j, iteratedDeriv (r j) (fun t => F t j) 0 / (Nat.factorial (r j) : ℂ)=1) →
        jetEvaluation (analyticJetAssignment F r (C+r i)) P ≠ 0 →
        analyticValues F=Set.range (greedy (weightAt r hr (by omega)))) := by
  obtain ⟨C,i,_,hmin,_,hC,_⟩ := generic_value_semigroup_theorem hd r hr
  have ht := (hC C).mpr le_rfl
  refine ⟨C,i,genericJetCondition r hr (by omega) (C+r i),hmin,
    genericJetCondition_ne_zero r hr (by omega) _,hC,?_,?_⟩
  · intro a ha
    exact normalized_generic_formal_values r hr (by omega) a i C ht ha
  · intro F hF ho hl hp
    exact generic_analytic_values_eq r hr (by omega) F hF ho hl i C ht hp

/-- Algebraic independence of all higher coefficients gives the claimed semigroup. -/
theorem release_algebraically_independent_values {d : ℕ} (hd : 2 ≤ d) (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (a : Fin d → ℕ → ℂ)
    (ha : AlgebraicIndependent ℚ (fun v : Fin d × ℕ => a v.1 (v.2+1))) :
    formalValues (normalizedFamily r a)=Set.range (greedy (weightAt r hr (by omega))) := by
  obtain ⟨C,i,_,_,_,hC,_⟩ := generic_value_semigroup_theorem hd r hr
  apply normalized_algebraicallyIndependent_values r hr (by omega) a i C ((hC C).mpr le_rfl)
  apply ha.comp (fun v : JetVariable d (C+r i) => (v.1, v.2.val))
  intro v w he
  apply Prod.ext
  · exact congrArg (fun x : Fin d × ℕ => x.1) he
  · apply Fin.ext
    exact congrArg (fun x : Fin d × ℕ => x.2) he

end GenericValueSemigroups
