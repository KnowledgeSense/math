import HonestEmbeddingDimension.BinomialCertificates

namespace HonestEmbeddingDimension

theorem binomial_coordinates_zero (m a b δ : ℕ) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) :
    ∀ i, (tripleCoordinates m (PowerSeries.X^a) (binomialCoordinate b δ) i).constantCoeff = 0 := by
  intro i
  fin_cases i <;> simp [tripleCoordinates,binomialCoordinate,Nat.ne_of_gt hm,Nat.ne_of_gt ha,Nat.ne_of_gt hb]

theorem binomial_first_value (m a b c δ u q : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (hu : m*u+b=q*a) (hc : q*a+δ=c) :
    c ∈ formalValues (tripleCoordinates m (PowerSeries.X^a) (binomialCoordinate b δ)) := by
  rw [formalValues_eq_polynomialValues _ (binomial_coordinates_zero m a b δ hm ha hb)]
  refine ⟨MvPolynomial.X 1^q-MvPolynomial.X 0^u*MvPolynomial.X 2,?_⟩
  simp only [map_sub,map_mul,map_pow,MvPolynomial.aeval_X]
  change ((PowerSeries.X^a)^q-(PowerSeries.X^m)^u*binomialCoordinate b δ).order = (c : ℕ∞)
  rw [binomial_first_cancellation m a b c δ u q hu hc]
  simp [PowerSeries.order_neg,PowerSeries.order_pow,nsmul_eq_mul]

theorem binomial_product_value (m a b c δ u : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (hu : m*u=a+b) (hc : a+b+δ=c) :
    c ∈ formalValues (tripleCoordinates m (PowerSeries.X^a) (binomialCoordinate b δ)) := by
  rw [formalValues_eq_polynomialValues _ (binomial_coordinates_zero m a b δ hm ha hb)]
  refine ⟨MvPolynomial.X 1*MvPolynomial.X 2-MvPolynomial.X 0^u,?_⟩
  simp only [map_sub,map_mul,map_pow,MvPolynomial.aeval_X]
  change (PowerSeries.X^a*binomialCoordinate b δ-(PowerSeries.X^m)^u).order = (c : ℕ∞)
  rw [binomial_product_cancellation m a b c δ u hu hc]
  simp [PowerSeries.order_pow,nsmul_eq_mul]

/-- The verified basis certificate together with the explicit cancellation determines all values. -/
theorem formal_binomial_values_of_certificate {q : ℕ} (S : AddSubmonoid ℕ) (m a b c δ N : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (B : Fin q → PowerSeries ℂ) (w : Fin q → ℕ)
    (hw : ∀ i, (B i).order = w i) (hwS : ∀ i, w i ∈ S)
    (hres : Function.Injective (fun i => w i % m))
    (htail : ∀ n, N ≤ n → n ∈ S) (e : Fin q) (he : B e=1)
    (hmul : ∀ i j, InParameterJetSpan m (Nat.ne_of_gt hm) B N
      (B j*tripleCoordinates m (PowerSeries.X^a) (binomialCoordinate b δ) i))
    (hgens : AddSubmonoid.closure ({m,a,b,c} : Set ℕ) = S)
    (hcval : c ∈ formalValues (tripleCoordinates m (PowerSeries.X^a) (binomialCoordinate b δ))) :
    formalValues (tripleCoordinates m (PowerSeries.X^a) (binomialCoordinate b δ)) = S := by
  let f := tripleCoordinates m (PowerSeries.X^a) (binomialCoordinate b δ)
  have hf0 := binomial_coordinates_zero m a b δ hm ha hb
  have hmS : m ∈ S := by rw [← hgens]; exact AddSubmonoid.subset_closure (by simp)
  have hcoord (i : Fin 3) (n : ℕ) (ho : (f i).order = n) : n ∈ formalValues f := by
    rw [formalValues_eq_polynomialValues f hf0]
    exact ⟨MvPolynomial.X i,by simpa using ho⟩
  apply formalValues_eq_of_parameter_basis (Nat.ne_of_gt hm) S hmS f hf0 B w hw hwS hres htail e he hmul
    {m,a,b,c} hgens
  intro n hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact hcoord 0 n (by simp [f,tripleCoordinates,PowerSeries.order_pow,nsmul_eq_mul])
  · exact hcoord 1 n (by simp [f,tripleCoordinates,PowerSeries.order_pow,nsmul_eq_mul])
  · exact hcoord 2 n (order_binomialCoordinate n δ hδ)
  · exact hcval

/-- The binomial realization uses actual entire coordinate functions. -/
theorem analytic_binomial_values_eq_formal (m a b δ : ℕ) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) :
    analyticValues (fun t : ℂ => ![t^m,t^a,t^b*(1+t^δ)]) =
      formalValues (tripleCoordinates m (PowerSeries.X^a) (binomialCoordinate b δ)) := by
  have hF : ∀ i : Fin 3, AnalyticAt ℂ (fun t : ℂ => (![t^m,t^a,t^b*(1+t^δ)] : Fin 3 → ℂ) i) 0 := by
    intro i
    fin_cases i
    · exact analyticAt_id.pow m
    · exact analyticAt_id.pow a
    · exact analyticAt_binomial b δ
  rw [analyticValues_eq_formalValues _ hF (by simp [Nat.ne_of_gt hm,Nat.ne_of_gt ha,Nat.ne_of_gt hb])]
  congr 1
  funext i
  fin_cases i
  · simpa [tripleCoordinates] using analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id m
  · simpa [tripleCoordinates] using analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id a
  · exact analyticTaylor_binomial b δ

end HonestEmbeddingDimension
