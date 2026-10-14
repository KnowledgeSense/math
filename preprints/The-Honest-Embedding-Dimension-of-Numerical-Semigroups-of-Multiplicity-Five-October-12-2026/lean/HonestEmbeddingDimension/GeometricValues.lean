import HonestEmbeddingDimension.GeometricCertificate

namespace HonestEmbeddingDimension

theorem formal_geometric_values (S : AddSubmonoid ℕ) (m a b c δ u v N : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (hu : m*u+b=2*a) (hc : 2*a+δ=c) (hv : m*v+c=a+b)
    (hZZ : N ≤ 2*b) (hYW : N ≤ a+c) (hZW : N ≤ b+c)
    (hgens : AddSubmonoid.closure ({m,a,b,c} : Set ℕ) = S)
    (hres : Function.Injective (fun i : Fin 4 => (![0,a,b,c] : Fin 4 → ℕ) i % m))
    (htail : ∀ n, N ≤ n → n ∈ S) :
    formalValues (tripleCoordinates m (PowerSeries.X^a) (PowerSeries.X^b*geometricUnit δ)) = S := by
  let f := tripleCoordinates m (PowerSeries.X^a) (PowerSeries.X^b*geometricUnit δ)
  have hf0 : ∀ i, (f i).constantCoeff = 0 := by
    intro i
    fin_cases i <;> simp [f,tripleCoordinates,Nat.ne_of_gt hm,Nat.ne_of_gt ha,Nat.ne_of_gt hb]
  have hS (n : ℕ) (hn : n ∈ ({m,a,b,c} : Set ℕ)) : n ∈ S := by
    rw [← hgens]
    exact AddSubmonoid.subset_closure hn
  have hwS : ∀ i : Fin 4, (![0,a,b,c] : Fin 4 → ℕ) i ∈ S := by
    intro i
    fin_cases i
    · exact S.zero_mem
    · exact hS a (by simp)
    · exact hS b (by simp)
    · exact hS c (by simp)
  have hsub : formalValues f ⊆ S :=
    formalValues_subset_of_parameter_basis (Nat.ne_of_gt hm) S (hS m (by simp)) f hf0
      (geometricBasis a b c δ) ![0,a,b,c] (order_geometricBasis a b c δ hδ) hwS hres htail 0 rfl
      (geometric_basis_multiplication m a b c δ u v N (Nat.ne_of_gt hm) hδ hu hc hv hZZ hYW hZW)
  have hcoord (i : Fin 3) (n : ℕ) (ho : (f i).order = n) : n ∈ formalValues f := by
    rw [formalValues_eq_polynomialValues f hf0]
    exact ⟨MvPolynomial.X i,by simpa using ho⟩
  have hmval : m ∈ formalValues f := hcoord 0 m (by simp [f,tripleCoordinates,PowerSeries.order_pow,nsmul_eq_mul])
  have haval : a ∈ formalValues f := hcoord 1 a (by simp [f,tripleCoordinates,PowerSeries.order_pow,nsmul_eq_mul])
  have hbval : b ∈ formalValues f := hcoord 2 b (by simp [f,tripleCoordinates,PowerSeries.order_mul,
    PowerSeries.order_pow,order_geometricUnit δ hδ,nsmul_eq_mul])
  have hcval : c ∈ formalValues f := by
    rw [formalValues_eq_polynomialValues f hf0]
    refine ⟨MvPolynomial.X 1 ^ 2-MvPolynomial.X 0 ^ u*MvPolynomial.X 2,?_⟩
    simp only [map_sub,map_mul,map_pow,MvPolynomial.aeval_X]
    change ((PowerSeries.X^a)^2-(PowerSeries.X^m)^u*(PowerSeries.X^b*geometricUnit δ)).order = (c : ℕ∞)
    rw [geometric_first_cancellation m a b c δ u hδ hu hc]
    simp [PowerSeries.order_mul,PowerSeries.order_neg,PowerSeries.order_pow,order_geometricUnit δ hδ,nsmul_eq_mul]
  apply Set.Subset.antisymm hsub
  change S ≤ formalValueSubmonoid f hf0
  rw [← hgens]
  apply AddSubmonoid.closure_le.mpr
  intro n hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact hmval
  · exact haval
  · exact hbval
  · exact hcval

/-- The rational construction is genuinely convergent and has the certified full value semigroup. -/
theorem analytic_geometric_values (S : AddSubmonoid ℕ) (m a b c δ u v N : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (hu : m*u+b=2*a) (hc : 2*a+δ=c) (hv : m*v+c=a+b)
    (hZZ : N ≤ 2*b) (hYW : N ≤ a+c) (hZW : N ≤ b+c)
    (hgens : AddSubmonoid.closure ({m,a,b,c} : Set ℕ) = S)
    (hres : Function.Injective (fun i : Fin 4 => (![0,a,b,c] : Fin 4 → ℕ) i % m))
    (htail : ∀ n, N ≤ n → n ∈ S) :
    analyticValues (fun t : ℂ => ![t^m,t^a,t^b/(1-t^δ)]) = S := by
  have hF : ∀ i : Fin 3, AnalyticAt ℂ (fun t : ℂ => (![t^m,t^a,t^b/(1-t^δ)] : Fin 3 → ℂ) i) 0 := by
    intro i
    fin_cases i
    · exact analyticAt_id.pow m
    · exact analyticAt_id.pow a
    · exact analyticAt_geometric_quotient b δ hδ
  rw [analyticValues_eq_formalValues _ hF (by
    simp [Nat.ne_of_gt hm,Nat.ne_of_gt ha,Nat.ne_of_gt hb])]
  have he : (fun i : Fin 3 => analyticTaylor
      (fun t : ℂ => (![t^m,t^a,t^b/(1-t^δ)] : Fin 3 → ℂ) i)) =
      tripleCoordinates m (PowerSeries.X^a) (PowerSeries.X^b*geometricUnit δ) := by
    funext i
    fin_cases i
    · simpa [tripleCoordinates] using analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id m
    · simpa [tripleCoordinates] using analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id a
    · exact analyticTaylor_geometric_quotient b δ hδ
  rw [he]
  exact formal_geometric_values S m a b c δ u v N hm ha hb hδ hu hc hv hZZ hYW hZW hgens hres htail

end HonestEmbeddingDimension
