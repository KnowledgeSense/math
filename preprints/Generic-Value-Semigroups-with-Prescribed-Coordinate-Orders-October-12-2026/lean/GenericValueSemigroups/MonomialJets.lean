import GenericValueSemigroups.JetRanks
import GenericValueSemigroups.WeightEnumeration

namespace GenericValueSemigroups
open scoped BigOperators Classical

noncomputable def monomialFamily {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (N : ℕ) : (weightSet r N) → PowerSeries ℂ :=
  fun α => coordinateMonomial f α.val

theorem aeval_monomial_coordinate {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (α : Fin d →₀ ℕ) (c : ℂ) :
    MvPolynomial.aeval f (MvPolynomial.monomial α c) = c • coordinateMonomial f α := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [Algebra.smul_def]; rfl

theorem polynomial_jet_in_monomial_span {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (hr : ∀ i, 0<r i) (hf : ∀ i, PowerSeries.order (f i)=r i)
    (N : ℕ) (P : MvPolynomial (Fin d) ℂ) :
    ∃ c : (weightSet r N) → ℂ, formalJet N (MvPolynomial.aeval f P) =
      formalJet N (seriesCombination (monomialFamily f r N) c) := by
  induction P using MvPolynomial.induction_on' with
  | monomial α a =>
    rw [aeval_monomial_coordinate]
    by_cases hα : (α : Fin d → ℕ) ∈ weightSet r N
    · refine ⟨Pi.single ⟨α,hα⟩ a, ?_⟩
      simp [seriesCombination, monomialFamily, Pi.single_apply]
    · refine ⟨0, ?_⟩
      have hw : N ≤ weight r α := by
        have h := (mem_weightSet r hr N α).not.mp hα
        omega
      ext j
      have hz : PowerSeries.coeff j (coordinateMonomial f α)=0 := by
        apply PowerSeries.coeff_of_lt_order
        rw [order_coordinateMonomial f r α hf]
        exact_mod_cast (lt_of_lt_of_le j.isLt hw)
      simp [formalJet, seriesCombination, hz]
  | add P Q hP hQ =>
    obtain ⟨c,hc⟩ := hP
    obtain ⟨e,he⟩ := hQ
    refine ⟨c+e, ?_⟩
    ext j
    have hcj := congrFun hc j
    have hej := congrFun he j
    simp only [formalJet] at hcj hej ⊢
    simp only [map_add]
    rw [hcj, hej]
    simp [seriesCombination, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem monomial_combination_is_polynomial {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (N : ℕ) (c : (weightSet r N) → ℂ) :
    ∃ P : MvPolynomial (Fin d) ℂ,
      MvPolynomial.aeval f P = seriesCombination (monomialFamily f r N) c := by
  refine ⟨∑ α, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α.val) (c α), ?_⟩
  simp only [map_sum, aeval_monomial_coordinate]
  rfl

theorem order_eq_of_jet_eq {N n : ℕ} {f g : PowerSeries ℂ}
    (h : formalJet N f = formalJet N g) (hn : n<N) :
    PowerSeries.order f=n ↔ PowerSeries.order g=n := by
  have hc (j : ℕ) (hj : j<N) : PowerSeries.coeff j f=PowerSeries.coeff j g :=
    congrFun h ⟨j,hj⟩
  simp only [PowerSeries.order_eq_nat]
  rw [hc n hn]
  apply and_congr_right
  intro _
  exact forall_congr' fun j => imp_congr_right fun hj => by rw [hc j (lt_trans hj hn)]

/-- Every value below the finite jet cutoff is detected by the actual monomial coefficient matrix. -/
theorem polynomial_value_iff_monomial_rank_step {d : ℕ}
    (f : Fin d → PowerSeries ℂ) (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (hf : ∀ i, PowerSeries.order (f i)=r i)
    (N n : ℕ) (hn : n<N) :
    n ∈ polynomialValues f ↔
      (coefficientMatrix (monomialFamily f r N) (n+1)).rank =
        (coefficientMatrix (monomialFamily f r N) n).rank+1 := by
  rw [← order_attained_iff_rank_step]
  constructor
  · rintro ⟨P,hP⟩
    obtain ⟨c,hc⟩ := polynomial_jet_in_monomial_span f r hr hf N P
    exact ⟨c,(order_eq_of_jet_eq hc hn).mp hP⟩
  · rintro ⟨c,hc⟩
    obtain ⟨P,hP⟩ := monomial_combination_is_polynomial f r N c
    exact ⟨P,by rw [hP]; exact hc⟩

end GenericValueSemigroups
