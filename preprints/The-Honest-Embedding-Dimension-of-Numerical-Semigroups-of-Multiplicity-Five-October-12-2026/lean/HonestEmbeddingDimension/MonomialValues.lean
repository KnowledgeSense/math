import HonestEmbeddingDimension.RationalGerms

namespace HonestEmbeddingDimension

noncomputable def monomialCoordinates {d : ℕ} (r : Fin d → ℕ) : Fin d → PowerSeries ℂ :=
  fun i => PowerSeries.X^(r i)

theorem monomial_polynomial_coeff_support {d : ℕ} (r : Fin d → ℕ)
    (P : MvPolynomial (Fin d) ℂ) (n : ℕ)
    (hn : n ∉ AddSubmonoid.closure (Set.range r)) :
    PowerSeries.coeff n (MvPolynomial.aeval (monomialCoordinates r) P) = 0 := by
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    have hw : (∑ i, r i*α i) ∈ AddSubmonoid.closure (Set.range r) := by
      apply AddSubmonoid.sum_mem
      intro i _
      have hi : r i ∈ AddSubmonoid.closure (Set.range r) := AddSubmonoid.subset_closure (Set.mem_range_self i)
      simpa [nsmul_eq_mul,Nat.mul_comm] using (AddSubmonoid.closure (Set.range r)).nsmul_mem hi (α i)
    have hne : n ≠ ∑ i, r i*α i := by intro he; exact hn (he ▸ hw)
    rw [MvPolynomial.aeval_monomial,Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [monomialCoordinates,← pow_mul,Finset.prod_pow_eq_pow_sum]
    simp [PowerSeries.coeff_X_pow,hne]
  | add P Q hP hQ => simp [hP,hQ]

theorem formal_monomial_values {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i) :
    formalValues (monomialCoordinates r) = (AddSubmonoid.closure (Set.range r) : Set ℕ) := by
  have hf0 : ∀ i, (monomialCoordinates r i).constantCoeff=0 := by
    intro i; simp [monomialCoordinates,Nat.ne_of_gt (hr i)]
  apply Set.Subset.antisymm
  · intro n hn
    rw [formalValues_eq_polynomialValues _ hf0] at hn
    obtain ⟨P,hP⟩ := hn
    by_contra hnot
    exact (PowerSeries.order_eq_nat.mp hP).1 (monomial_polynomial_coeff_support r P n hnot)
  · change AddSubmonoid.closure (Set.range r) ≤ formalValueSubmonoid (monomialCoordinates r) hf0
    apply AddSubmonoid.closure_le.mpr
    rintro n ⟨i,rfl⟩
    change r i ∈ formalValues (monomialCoordinates r)
    rw [formalValues_eq_polynomialValues _ hf0]
    refine ⟨MvPolynomial.X i,?_⟩
    simp [monomialCoordinates,PowerSeries.order_pow,nsmul_eq_mul]

/-- Monomial realizations give actual convergent value algebras, not only formal examples. -/
theorem analytic_monomial_values {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i) :
    analyticValues (fun t : ℂ => fun i => t^(r i)) = (AddSubmonoid.closure (Set.range r) : Set ℕ) := by
  rw [analyticValues_eq_formalValues (fun t : ℂ => fun i => t^(r i)) (fun i => analyticAt_id.pow (r i)) (by
    funext i; simp [Nat.ne_of_gt (hr i)])]
  have he : (fun i => analyticTaylor (fun t : ℂ => t^(r i))) = monomialCoordinates r := by
    funext i
    simpa [monomialCoordinates] using analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id (r i)
  rw [he]
  exact formal_monomial_values r hr

theorem monomial_analytic_realization {S : NumericalSemigroup} {d : ℕ}
    (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hgens : AddSubmonoid.closure (Set.range r) = S.monoid) : AnalyticallyRealizes S d := by
  refine ⟨fun t : ℂ => fun i => t^(r i),fun i => analyticAt_id.pow (r i),?_,?_⟩
  · funext i; simp [Nat.ne_of_gt (hr i)]
  · rw [analytic_monomial_values r hr,hgens]

end HonestEmbeddingDimension
