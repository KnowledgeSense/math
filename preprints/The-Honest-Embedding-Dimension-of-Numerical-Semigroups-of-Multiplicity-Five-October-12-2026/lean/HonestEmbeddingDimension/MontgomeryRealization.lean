import HonestEmbeddingDimension.MontgomeryJet

namespace HonestEmbeddingDimension

/-- Montgomery's four-coordinate binomial germ has exactly the original numerical semigroup.
The no-extra-values direction uses the actual Apéry basis, not a supplied realization hypothesis. -/
theorem formal_montgomery_values {S : NumericalSemigroup} {a b c d δ u : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d)
    (s : Fin 3) (hs0 : s ≠ 0) (hδ : 0 < δ)
    (hu : 5 * u + ![a, b, c] s = 2 * a) (hd : 2 * a + δ = d) :
    formalValues (parameterCoordinates 5 (montgomeryAux ![a, b, c] δ s)) = S.monoid := by
  let w : Fin 3 → ℕ := ![a, b, c]
  let f := parameterCoordinates 5 (montgomeryAux w δ s)
  let B := linearParameterBasis (montgomeryAux w δ s)
  obtain ⟨h5, ha, hb, hc, _⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hwpos : ∀ i, 0 < w i := by intro i; fin_cases i <;> dsimp [w] <;> omega
  have hwlow : ∀ i, a ≤ w i := by intro i; fin_cases i <;> dsimp [w] <;> omega
  have hwS : ∀ i, w i ∈ S.monoid := by
    intro i
    fin_cases i
    · exact ha.2.1
    · exact hb.2.1
    · exact hc.2.1
  have hf0 : ∀ i, (f i).constantCoeff = 0 := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [f, parameterCoordinates]
    · apply PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
      change (1 : ℕ∞) ≤ (montgomeryAux w δ s i).order
      rw [order_montgomeryAux w δ s i hδ]
      exact_mod_cast hwpos i
  have hBord : ∀ i : Fin 4, (B i).order = (![0, a, b, c] : Fin 4 → ℕ) i := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [B, linearParameterBasis]
    · exact order_montgomeryAux w δ s i hδ
  have hBS : ∀ i : Fin 4, (![0, a, b, c] : Fin 4 → ℕ) i ∈ S.monoid := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact S.monoid.zero_mem
    · exact hwS i
  have htail : ∀ n, d ≤ n → n ∈ S.monoid := by
    intro n hn
    apply S.mem_of_conductor_le
    rw [(five_generator_aperyMax_conductor_general hm h).2]
    omega
  have hreduce : ∀ n ∈ S.monoid, n < d →
      ∃ j : Fin 4, ∃ q : ℕ, n = 5 * q + (Fin.cons (α := fun _ => ℕ) 0 w) j := by
    intro n hn hnd
    exact five_generator_reduction_below_last hm h hn hnd
  have hsub : formalValues f ⊆ S.monoid :=
    formalValues_subset_of_parameter_basis (by omega) S.monoid hm.2.1 f hf0 B ![0, a, b, c]
      hBord hBS (five_generator_first_four_residues_injective hm h) htail 0 rfl
      (montgomery_basis_multiplication S.monoid w a δ d s hd hwlow hwS hreduce)
  have hcoord (i : Fin 4) (n : ℕ) (ho : (f i).order = n) : n ∈ formalValues f := by
    rw [formalValues_eq_polynomialValues f hf0]
    exact ⟨MvPolynomial.X i, by simpa using ho⟩
  have h5val : 5 ∈ formalValues f := hcoord 0 5 (by
    simp [f, parameterCoordinates, PowerSeries.order_pow, nsmul_eq_mul])
  have hwval (i : Fin 3) : w i ∈ formalValues f :=
    hcoord i.succ (w i) (order_montgomeryAux w δ s i hδ)
  have hdval : d ∈ formalValues f := by
    rw [formalValues_eq_polynomialValues f hf0]
    refine ⟨MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ u * MvPolynomial.X s.succ, ?_⟩
    simp only [map_sub, map_mul, map_pow, MvPolynomial.aeval_X]
    change ((montgomeryAux w δ s 0) ^ 2 - (PowerSeries.X ^ 5) ^ u * montgomeryAux w δ s s).order = (d : ℕ∞)
    have hz : montgomeryAux w δ s 0 = PowerSeries.X ^ a := by
      simp [montgomeryAux, Ne.symm hs0, w]
    have hs : montgomeryAux w δ s s = binomialCoordinate (w s) δ := by simp [montgomeryAux]
    rw [hz, hs, binomial_first_cancellation 5 a (w s) d δ u 2 hu hd]
    simp [PowerSeries.order_neg, PowerSeries.order_pow, nsmul_eq_mul]
  apply Set.Subset.antisymm hsub
  change S.monoid ≤ formalValueSubmonoid f hf0
  rw [← h.generates]
  apply AddSubmonoid.closure_le.mpr
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact h5val
  · exact hwval 0
  · exact hwval 1
  · exact hwval 2
  · exact hdval

/-- The convergent polynomial germ implementing Montgomery's construction. -/
noncomputable def montgomeryGerm (w : Fin 3 → ℕ) (δ : ℕ) (s : Fin 3) : ℂ → Fin 4 → ℂ :=
  fun t => Fin.cons (t ^ 5) (fun i => if i = s then t ^ (w i) * (1 + t ^ δ) else t ^ (w i))

theorem analyticAt_montgomeryGerm (w : Fin 3 → ℕ) (δ : ℕ) (s : Fin 3) (i : Fin 4) :
    AnalyticAt ℂ (fun t => montgomeryGerm w δ s t i) 0 := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact analyticAt_id.pow 5
  · change AnalyticAt ℂ (fun t : ℂ => if i = s then t ^ (w i) * (1 + t ^ δ) else t ^ (w i)) 0
    by_cases hi : i = s
    · simp only [ite_eq_left hi]
      exact analyticAt_binomial (w i) δ
    · simp only [ite_eq_right hi]
      exact analyticAt_id.pow (w i)

theorem montgomeryGerm_zero (w : Fin 3 → ℕ) (δ : ℕ) (s : Fin 3)
    (hw : ∀ i, 0 < w i) : montgomeryGerm w δ s 0 = 0 := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [montgomeryGerm]
  · simp [montgomeryGerm, Nat.ne_of_gt (hw i)]

theorem analyticTaylor_montgomeryGerm (w : Fin 3 → ℕ) (δ : ℕ) (s : Fin 3) :
    (fun i => analyticTaylor (fun t => montgomeryGerm w δ s t i)) =
      parameterCoordinates 5 (montgomeryAux w δ s) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa [montgomeryGerm, parameterCoordinates] using analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id 5
  · by_cases hi : i = s
    · simpa [montgomeryGerm, parameterCoordinates, montgomeryAux, hi] using analyticTaylor_binomial (w i) δ
    · simpa [montgomeryGerm, parameterCoordinates, montgomeryAux, hi] using
        analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id (w i)

/-- The nonmaximal case of Montgomery's theorem for every intrinsic multiplicity-five semigroup.
The original four-coordinate polynomial parametrization is certified analytically and formally. -/
theorem analytic_realization_five_nonmaximal {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) (hdgt : 2 * a < d) :
    AnalyticallyRealizes S 4 := by
  obtain ⟨s, hs0, hsmod, hslt⟩ := montgomery_exceptional_generator hm h hdgt
  have hδ : 0 < d - 2 * a := by omega
  obtain ⟨_, hu⟩ := positive_five_quotient hslt hsmod
  have hw : ∀ i : Fin 3, 0 < (![a, b, c] : Fin 3 → ℕ) i := by
    intro i
    have h5a := h.five_lt_a
    have hab := h.a_lt_b
    have hbc := h.b_lt_c
    fin_cases i <;> dsimp <;> omega
  refine ⟨montgomeryGerm ![a, b, c] (d - 2 * a) s,
    analyticAt_montgomeryGerm _ _ _, montgomeryGerm_zero _ _ _ hw, ?_⟩
  rw [analyticValues_eq_formalValues _ (analyticAt_montgomeryGerm _ _ _)
    (montgomeryGerm_zero _ _ _ hw), analyticTaylor_montgomeryGerm]
  exact formal_montgomery_values hm h s hs0 hδ hu (by omega)

end HonestEmbeddingDimension
