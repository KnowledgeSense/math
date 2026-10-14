import HonestEmbeddingDimension.BinomialValues
import HonestEmbeddingDimension.RemainingConstructionArithmetic

namespace HonestEmbeddingDimension

theorem analytic_binomial_realization_of_values {S : NumericalSemigroup} (a b δ : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hvalues : formalValues (tripleCoordinates 5 (PowerSeries.X^a) (binomialCoordinate b δ)) = S.monoid) :
    AnalyticallyRealizes S 3 := by
  refine ⟨fun t : ℂ => ![t^5,t^a,t^b*(1+t^δ)],?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact analyticAt_id.pow 5
    · exact analyticAt_id.pow a
    · exact analyticAt_binomial b δ
  · simp [Nat.ne_of_gt ha,Nat.ne_of_gt hb]
  · rw [analytic_binomial_values_eq_formal 5 a b δ (by omega) ha hb]
    exact hvalues

/-- Source case 4B, including its complete no-extra-values proof. -/
theorem analytic_realization_case_4B {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b%5=(2*a)%5) (hc : c%5=(4*a)%5) (hca : 2*a<c) : AnalyticallyRealizes S 3 := by
  have ha0 : 0<a := by have := h.five_lt_a; omega
  have hb0 : 0<b := by have := h.a_lt_b; omega
  obtain ⟨hδ,_,hu,hYYZ,hYW,hZZ,hYZZ,hZW⟩ := four_generator_parameters_4B h hb hc hca
  have hcond := (four_generator_conductor_4B hm h hb hc hca).2
  let B := fiveBasis (PowerSeries.X^a) (binomialCoordinate b (c-2*a)) (-PowerSeries.X^c)
  have hw : ∀ i, (B i).order = (![0,a,b,a+b,c] : Fin 5 → ℕ) i := by
    intro i
    fin_cases i <;> simp [B,fiveBasis,PowerSeries.order_mul,PowerSeries.order_pow,PowerSeries.order_neg,
      order_binomialCoordinate b (c-2*a) hδ,nsmul_eq_mul]
  have hwS : ∀ i : Fin 5, (![0,a,b,a+b,c] : Fin 5 → ℕ) i ∈ S.monoid := by
    intro i
    fin_cases i
    · exact S.monoid.zero_mem
    · exact h.minimal.2.1.2.1
    · exact h.minimal.2.2.1.2.1
    · exact S.monoid.add_mem h.minimal.2.1.2.1 h.minimal.2.2.1.2.1
    · exact h.minimal.2.2.2.2.1
  apply analytic_binomial_realization_of_values a b (c-2*a) ha0 hb0
  apply formal_binomial_values_of_certificate S.monoid 5 a b c (c-2*a) (max (a+b) c)
    (by omega) ha0 hb0 hδ B ![0,a,b,a+b,c] hw hwS (four_generator_basis_residues_4B hm h hb hc hca)
    _ 0 rfl (binomial_basis_4B 5 a b c (c-2*a) ((2*a-b)/5) (max (a+b) c)
      (by omega) hδ hu (by omega) hYYZ hYW hZZ hYZZ hZW) h.generates
    (binomial_first_value 5 a b c (c-2*a) ((2*a-b)/5) 2 (by omega) ha0 hb0 hu (by omega))
  intro n hn
  apply S.mem_of_conductor_le
  rw [hcond]
  omega

theorem power_binomial_basis_orders (a b δ : ℕ) (hδ : 0<δ) (i : Fin 4) :
    (powerBasis (PowerSeries.X^a) (binomialCoordinate b δ) i).order =
      (![0,a,2*a,b] : Fin 4 → ℕ) i := by
  fin_cases i <;> simp [powerBasis,PowerSeries.order_pow,nsmul_eq_mul,order_binomialCoordinate b δ hδ,mul_comm]

theorem HasFourGenerators.power_basis_mem {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c) (i : Fin 4) : (![0,a,2*a,b] : Fin 4 → ℕ) i ∈ S.monoid := by
  fin_cases i
  · exact S.monoid.zero_mem
  · exact h.minimal.2.1.2.1
  · change 2*a ∈ S.monoid
    simpa only [two_mul] using S.monoid.add_mem h.minimal.2.1.2.1 h.minimal.2.1.2.1
  · exact h.minimal.2.2.1.2.1

/-- Source case 4C, with actual entire binomial coordinates. -/
theorem analytic_realization_case_4C {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b%5=(3*a)%5) (hc : c%5=(4*a)%5) (hca : 3*a<c) : AnalyticallyRealizes S 3 := by
  have ha0 : 0<a := by have := h.five_lt_a; omega
  have hb0 : 0<b := by have := h.a_lt_b; omega
  obtain ⟨hδ,_,hu,hYZ,hYYZ,hZZ⟩ := four_generator_parameters_4C h hb hc hca
  have hcond := (four_generator_conductor_4C hm h hb hc hca).2
  apply analytic_binomial_realization_of_values a b (c-3*a) ha0 hb0
  apply formal_binomial_values_of_certificate S.monoid 5 a b c (c-3*a) c
    (by omega) ha0 hb0 hδ (powerBasis (PowerSeries.X^a) (binomialCoordinate b (c-3*a))) ![0,a,2*a,b]
    (power_binomial_basis_orders a b (c-3*a) hδ) h.power_basis_mem
    (four_generator_basis_residues_4C hm h hb hc hca) _ 0 rfl
    (binomial_basis_4C 5 a b c (c-3*a) ((3*a-b)/5) (by omega) hδ hu (by omega) hYZ hYYZ hZZ)
    h.generates (binomial_first_value 5 a b c (c-3*a) ((3*a-b)/5) 3 (by omega) ha0 hb0 hu (by omega))
  intro n hn
  apply S.mem_of_conductor_le
  rw [hcond]
  omega

/-- Source case 4D, with the exact product cancellation. -/
theorem analytic_realization_case_4D {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b%5=(4*a)%5) (hc : c%5=(3*a)%5) (hca : a+b<c) : AnalyticallyRealizes S 3 := by
  have ha0 : 0<a := by have := h.five_lt_a; omega
  have hb0 : 0<b := by have := h.a_lt_b; omega
  obtain ⟨hδ,_,hu,hYYY,hYYZ,hZZ⟩ := four_generator_parameters_4D h hb hc hca
  have hcond := (four_generator_conductor_4D hm h hb hc hca).2
  apply analytic_binomial_realization_of_values a b (c-a-b) ha0 hb0
  apply formal_binomial_values_of_certificate S.monoid 5 a b c (c-a-b) c
    (by omega) ha0 hb0 hδ (powerBasis (PowerSeries.X^a) (binomialCoordinate b (c-a-b))) ![0,a,2*a,b]
    (power_binomial_basis_orders a b (c-a-b) hδ) h.power_basis_mem
    (four_generator_basis_residues_4D hm h hb hc hca) _ 0 rfl
    (binomial_basis_4D 5 a b c (c-a-b) ((a+b)/5) (by omega) hδ hu (by omega) hYYY hYYZ hZZ)
    h.generates (binomial_product_value 5 a b c (c-a-b) ((a+b)/5) (by omega) ha0 hb0 hu (by omega))
  intro n hn
  apply S.mem_of_conductor_le
  rw [hcond]
  omega

end HonestEmbeddingDimension
