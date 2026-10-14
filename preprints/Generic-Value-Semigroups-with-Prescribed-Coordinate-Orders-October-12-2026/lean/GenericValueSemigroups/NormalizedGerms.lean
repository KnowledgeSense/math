import GenericValueSemigroups.GenericSemigroup
import GenericValueSemigroups.AnalyticTaylor

namespace GenericValueSemigroups

/-- The original coordinate form t^r(1+∑_{k≥1}a_k t^k), with completely arbitrary higher tail. -/
noncomputable def normalizedFamily {d : ℕ} (r : Fin d → ℕ) (a : Fin d → ℕ → ℂ)
    (i : Fin d) : PowerSeries ℂ :=
  PowerSeries.X^(r i) * (1 + PowerSeries.mk (fun k => if k=0 then 0 else a i k))

theorem normalizedFamily_below {d : ℕ} (r : Fin d → ℕ) (a : Fin d → ℕ → ℂ)
    (i : Fin d) (n : ℕ) (hn : n < r i) : PowerSeries.coeff n (normalizedFamily r a i)=0 := by
  simp [normalizedFamily, PowerSeries.coeff_X_pow_mul', Nat.not_le.mpr hn]

@[simp] theorem normalizedFamily_leading {d : ℕ} (r : Fin d → ℕ) (a : Fin d → ℕ → ℂ)
    (i : Fin d) : PowerSeries.coeff (r i) (normalizedFamily r a i)=1 := by
  simp [normalizedFamily, PowerSeries.coeff_X_pow_mul']

theorem normalizedFamily_order {d : ℕ} (r : Fin d → ℕ) (a : Fin d → ℕ → ℂ)
    (i : Fin d) : PowerSeries.order (normalizedFamily r a i)=r i := by
  apply PowerSeries.order_eq_nat.mpr
  exact ⟨by simp, fun n hn => normalizedFamily_below r a i n hn⟩

theorem normalizedFamily_higher {d : ℕ} (r : Fin d → ℕ) (a : Fin d → ℕ → ℂ)
    (i : Fin d) (k : ℕ) (hk : 0 < k) :
    PowerSeries.coeff (r i+k) (normalizedFamily r a i)=a i k := by
  simp [normalizedFamily, PowerSeries.coeff_X_pow_mul', Nat.ne_of_gt hk]

@[simp] theorem jetAssignment_normalizedFamily {d N : ℕ} (r : Fin d → ℕ)
    (a : Fin d → ℕ → ℂ) :
    jetAssignment (normalizedFamily r a) r N = (fun v => a v.1 (v.2.val+1)) := by
  funext v
  exact normalizedFamily_higher r a v.1 (v.2.val+1) (Nat.succ_pos _)

/-- The generic formal theorem for the exact coordinate expression in the release paper. -/
theorem normalized_generic_formal_values {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (a : Fin d → ℕ → ℂ) (i : Fin d) (C : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ Set.range (greedy (weightAt r hr hd)))
    (hcondition : jetEvaluation (fun v => a v.1 (v.2.val+1))
      (genericJetCondition r hr hd (C+r i)) ≠ 0) :
    formalValues (normalizedFamily r a) = Set.range (greedy (weightAt r hr hd)) := by
  apply generic_formal_values_eq _ r hr hd (normalizedFamily_order r a)
    (normalizedFamily_leading r a) i C hC
  simpa using hcondition

/-- All coefficients at and beyond the finite jet bound are unrestricted. -/
theorem normalized_generic_tail_independent {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (a b : Fin d → ℕ → ℂ) (i : Fin d) (C : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ Set.range (greedy (weightAt r hr hd)))
    (hcondition : jetEvaluation (fun v => a v.1 (v.2.val+1))
      (genericJetCondition r hr hd (C+r i)) ≠ 0)
    (hab : ∀ j k, 0 < k → k < C+r i → a j k=b j k) :
    formalValues (normalizedFamily r b) = Set.range (greedy (weightAt r hr hd)) := by
  apply normalized_generic_formal_values r hr hd b i C hC
  convert hcondition using 2
  congr 1
  funext v
  exact (hab v.1 (v.2.val+1) (Nat.succ_pos _) (by have := v.2.isLt; omega)).symm

/-- Algebraic independence over ℚ suffices for the original normalized formal family. -/
theorem normalized_algebraicallyIndependent_values {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (a : Fin d → ℕ → ℂ) (i : Fin d) (C : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ Set.range (greedy (weightAt r hr hd)))
    (ha : AlgebraicIndependent ℚ (fun v : JetVariable d (C+r i) => a v.1 (v.2.val+1))) :
    formalValues (normalizedFamily r a) = Set.range (greedy (weightAt r hr hd)) := by
  apply normalized_generic_formal_values r hr hd a i C hC
  exact jetEvaluation_ne_zero_of_algebraicIndependent _ ha _ (genericJetCondition_ne_zero r hr hd _)

/-- Transfer to the genuine convergent analytic algebra through its actual Taylor series. -/
theorem normalized_generic_analytic_values {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (a : Fin d → ℕ → ℂ)
    (F : ℂ → Fin d → ℂ) (hF : ∀ j, AnalyticAt ℂ (fun t => F t j) 0) (hF0 : F 0=0)
    (htaylor : ∀ j, analyticTaylor (fun t => F t j)=normalizedFamily r a j)
    (i : Fin d) (C : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ Set.range (greedy (weightAt r hr hd)))
    (hcondition : jetEvaluation (fun v => a v.1 (v.2.val+1))
      (genericJetCondition r hr hd (C+r i)) ≠ 0) :
    analyticValues F = Set.range (greedy (weightAt r hr hd)) := by
  rw [analyticValues_eq_formalValues F hF hF0]
  have he : (fun j => analyticTaylor (fun t => F t j))=normalizedFamily r a := funext htaylor
  rw [he]
  exact normalized_generic_formal_values r hr hd a i C hC hcondition

noncomputable def analyticJetAssignment {d : ℕ} (F : ℂ → Fin d → ℂ)
    (r : Fin d → ℕ) (N : ℕ) : JetVariable d N → ℂ :=
  fun v => iteratedDeriv (r v.1+v.2.val+1) (fun t => F t v.1) 0 /
    (Nat.factorial (r v.1+v.2.val+1) : ℂ)

/-- The analytic version stated entirely in terms of actual analytic functions and derivatives. -/
theorem generic_analytic_values_eq {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (F : ℂ → Fin d → ℂ)
    (hF : ∀ j, AnalyticAt ℂ (fun t => F t j) 0)
    (horder : ∀ j, analyticOrderAt (fun t => F t j) 0=r j)
    (hlead : ∀ j, iteratedDeriv (r j) (fun t => F t j) 0 / (Nat.factorial (r j) : ℂ)=1)
    (i : Fin d) (C : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ Set.range (greedy (weightAt r hr hd)))
    (hcondition : jetEvaluation (analyticJetAssignment F r (C+r i))
      (genericJetCondition r hr hd (C+r i)) ≠ 0) :
    analyticValues F = Set.range (greedy (weightAt r hr hd)) := by
  let f : Fin d → PowerSeries ℂ := fun j => analyticTaylor (fun t => F t j)
  have hf : ∀ j, PowerSeries.order (f j)=r j := fun j =>
    (order_analyticTaylor (hF j)).trans (horder j)
  have hF0 : F 0=0 := by
    funext j
    have hc : PowerSeries.coeff 0 (f j)=0 := by
      apply PowerSeries.coeff_of_lt_order
      rw [hf]
      exact_mod_cast hr j
    simpa [f] using hc
  rw [analyticValues_eq_formalValues F hF hF0]
  apply generic_formal_values_eq f r hr hd hf (fun j => by simpa [f] using hlead j) i C hC
  have he : jetAssignment f r (C+r i)=analyticJetAssignment F r (C+r i) := by
    funext v
    exact coeff_analyticTaylor (fun t => F t v.1) (r v.1+v.2.val+1)
  rw [he]
  exact hcondition

theorem algebraicallyIndependent_analytic_values {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (F : ℂ → Fin d → ℂ)
    (hF : ∀ j, AnalyticAt ℂ (fun t => F t j) 0)
    (horder : ∀ j, analyticOrderAt (fun t => F t j) 0=r j)
    (hlead : ∀ j, iteratedDeriv (r j) (fun t => F t j) 0 / (Nat.factorial (r j) : ℂ)=1)
    (i : Fin d) (C : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ Set.range (greedy (weightAt r hr hd)))
    (ha : AlgebraicIndependent ℚ (analyticJetAssignment F r (C+r i))) :
    analyticValues F = Set.range (greedy (weightAt r hr hd)) := by
  apply generic_analytic_values_eq r hr hd F hF horder hlead i C hC
  exact jetEvaluation_ne_zero_of_algebraicIndependent _ ha _ (genericJetCondition_ne_zero r hr hd _)

end GenericValueSemigroups
