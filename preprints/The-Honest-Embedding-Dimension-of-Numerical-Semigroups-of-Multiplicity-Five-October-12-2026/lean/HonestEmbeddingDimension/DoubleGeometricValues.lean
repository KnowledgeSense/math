import HonestEmbeddingDimension.DoubleGeometricCertificate

namespace HonestEmbeddingDimension

theorem formal_double_geometric_values (S : AddSubmonoid ℕ) (m a b c d δ ε u v : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) (hε : 0 < ε)
    (hu : m*u+b=2*a) (hc : 2*a+δ=c) (hv : m*v+c=a+b) (hd : a+b+ε=d)
    (hZZ : d ≤ 2*b) (hYW : d ≤ a+c) (hZW : d ≤ b+c)
    (hgens : AddSubmonoid.closure ({m,a,b,c,d} : Set ℕ) = S)
    (hres : Function.Injective (fun i : Fin 4 => (![0,a,b,c] : Fin 4 → ℕ) i % m))
    (htail : ∀ n, d ≤ n → n ∈ S) :
    formalValues (tripleCoordinates m (PowerSeries.X^a) (doubleGeometricZ b δ ε)) = S := by
  let f := tripleCoordinates m (PowerSeries.X^a) (doubleGeometricZ b δ ε)
  let B := fourBasis (PowerSeries.X^a) (doubleGeometricZ b δ ε) (doubleGeometricW c δ ε)
  have hf0 : ∀ i, (f i).constantCoeff = 0 := by
    intro i
    fin_cases i <;> simp [f,tripleCoordinates,doubleGeometricZ,Nat.ne_of_gt hm,Nat.ne_of_gt ha,Nat.ne_of_gt hb]
  have hS (n : ℕ) (hn : n ∈ ({m,a,b,c,d} : Set ℕ)) : n ∈ S := by
    rw [← hgens]
    exact AddSubmonoid.subset_closure hn
  have hw : ∀ i, (B i).order = (![0,a,b,c] : Fin 4 → ℕ) i := by
    intro i
    fin_cases i <;> simp [B,fourBasis,PowerSeries.order_pow,nsmul_eq_mul,
      order_doubleGeometricZ b δ ε hδ,order_doubleGeometricW c δ ε hδ hε]
  have hwS : ∀ i : Fin 4, (![0,a,b,c] : Fin 4 → ℕ) i ∈ S := by
    intro i
    fin_cases i
    · exact S.zero_mem
    · exact hS a (by simp)
    · exact hS b (by simp)
    · exact hS c (by simp)
  have hcoord (i : Fin 3) (n : ℕ) (ho : (f i).order = n) : n ∈ formalValues f := by
    rw [formalValues_eq_polynomialValues f hf0]
    exact ⟨MvPolynomial.X i,by simpa using ho⟩
  have hmval : m ∈ formalValues f := hcoord 0 m (by simp [f,tripleCoordinates,PowerSeries.order_pow,nsmul_eq_mul])
  have haval : a ∈ formalValues f := hcoord 1 a (by simp [f,tripleCoordinates,PowerSeries.order_pow,nsmul_eq_mul])
  have hbval : b ∈ formalValues f := hcoord 2 b (order_doubleGeometricZ b δ ε hδ)
  have hcval : c ∈ formalValues f := by
    rw [formalValues_eq_polynomialValues f hf0]
    refine ⟨MvPolynomial.X 1 ^ 2-MvPolynomial.X 0 ^ u*MvPolynomial.X 2,?_⟩
    simp only [map_sub,map_mul,map_pow,MvPolynomial.aeval_X]
    change ((PowerSeries.X^a)^2-(PowerSeries.X^m)^u*doubleGeometricZ b δ ε).order = (c : ℕ∞)
    rw [double_geometric_first_cancellation m a b c δ ε u hδ hu hc]
    exact order_doubleGeometricW c δ ε hδ hε
  have hdval : d ∈ formalValues f := by
    rw [formalValues_eq_polynomialValues f hf0]
    refine ⟨MvPolynomial.X 1*MvPolynomial.X 2+
      MvPolynomial.X 0^v*(MvPolynomial.X 1^2-MvPolynomial.X 0^u*MvPolynomial.X 2),?_⟩
    simp only [map_add,map_sub,map_mul,map_pow,MvPolynomial.aeval_X]
    change (PowerSeries.X^a*doubleGeometricZ b δ ε+(PowerSeries.X^m)^v*
      ((PowerSeries.X^a)^2-(PowerSeries.X^m)^u*doubleGeometricZ b δ ε)).order = (d : ℕ∞)
    rw [double_geometric_first_cancellation m a b c δ ε u hδ hu hc,
      double_geometric_second_cancellation m a b c d δ ε v hδ hv hd]
    simp [PowerSeries.order_neg,PowerSeries.order_pow,nsmul_eq_mul]
  apply formalValues_eq_of_parameter_basis (Nat.ne_of_gt hm) S (hS m (by simp)) f hf0 B ![0,a,b,c]
    hw hwS hres htail 0 rfl
    (double_geometric_basis_multiplication m a b c d δ ε u v (Nat.ne_of_gt hm) hδ hε hu hc hv hd hZZ hYW hZW)
    {m,a,b,c,d} hgens
  intro n hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact hmval
  · exact haval
  · exact hbval
  · exact hcval
  · exact hdval

theorem analyticAt_double_geometric (b δ ε : ℕ) (hδ : 0 < δ) :
    AnalyticAt ℂ (fun t : ℂ => t^b*(1+t^(δ+ε))/(1-t^δ)) 0 := by
  apply ((analyticAt_id.pow b).mul (analyticAt_const.add (analyticAt_id.pow (δ+ε)))).div
    (analyticAt_const.sub (analyticAt_id.pow δ))
  simp [Nat.ne_of_gt hδ]

theorem analyticTaylor_double_geometric (b δ ε : ℕ) (hδ : 0 < δ) :
    analyticTaylor (fun t : ℂ => t^b*(1+t^(δ+ε))/(1-t^δ)) = doubleGeometricZ b δ ε := by
  rw [analyticTaylor_div (f := fun t : ℂ => t^b*(1+t^(δ+ε))) (g := fun t => 1-t^δ)
    ((analyticAt_id.pow b).mul (analyticAt_const.add (analyticAt_id.pow (δ+ε))))
    (analyticAt_const.sub (analyticAt_id.pow δ)) (by simp [Nat.ne_of_gt hδ])]
  rw [analyticTaylor_mul (f := fun t : ℂ => t^b) (g := fun t => 1+t^(δ+ε))
    (analyticAt_id.pow b) (analyticAt_const.add (analyticAt_id.pow (δ+ε)))]
  rw [analyticTaylor_add (f := fun _ : ℂ => 1) (g := fun t => t^(δ+ε)) analyticAt_const (analyticAt_id.pow (δ+ε)),
    analyticTaylor_sub (f := fun _ : ℂ => 1) (g := fun t => t^δ) analyticAt_const (analyticAt_id.pow δ)]
  simp [analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id,doubleGeometricZ,geometricUnit]

/-- The five-generator rational construction has the exact convergent value algebra. -/
theorem analytic_double_geometric_values (S : AddSubmonoid ℕ) (m a b c d δ ε u v : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) (hε : 0 < ε)
    (hu : m*u+b=2*a) (hc : 2*a+δ=c) (hv : m*v+c=a+b) (hd : a+b+ε=d)
    (hZZ : d ≤ 2*b) (hYW : d ≤ a+c) (hZW : d ≤ b+c)
    (hgens : AddSubmonoid.closure ({m,a,b,c,d} : Set ℕ) = S)
    (hres : Function.Injective (fun i : Fin 4 => (![0,a,b,c] : Fin 4 → ℕ) i % m))
    (htail : ∀ n, d ≤ n → n ∈ S) :
    analyticValues (fun t : ℂ => ![t^m,t^a,t^b*(1+t^(δ+ε))/(1-t^δ)]) = S := by
  have hF : ∀ i : Fin 3, AnalyticAt ℂ
      (fun t : ℂ => (![t^m,t^a,t^b*(1+t^(δ+ε))/(1-t^δ)] : Fin 3 → ℂ) i) 0 := by
    intro i
    fin_cases i
    · exact analyticAt_id.pow m
    · exact analyticAt_id.pow a
    · exact analyticAt_double_geometric b δ ε hδ
  rw [analyticValues_eq_formalValues _ hF (by
    simp [Nat.ne_of_gt hm,Nat.ne_of_gt ha,Nat.ne_of_gt hb])]
  have he : (fun i : Fin 3 => analyticTaylor
      (fun t : ℂ => (![t^m,t^a,t^b*(1+t^(δ+ε))/(1-t^δ)] : Fin 3 → ℂ) i)) =
      tripleCoordinates m (PowerSeries.X^a) (doubleGeometricZ b δ ε) := by
    funext i
    fin_cases i
    · simpa [tripleCoordinates] using analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id m
    · simpa [tripleCoordinates] using analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id a
    · exact analyticTaylor_double_geometric b δ ε hδ
  rw [he]
  exact formal_double_geometric_values S m a b c d δ ε u v hm ha hb hδ hε hu hc hv hd hZZ hYW hZW hgens hres htail

end HonestEmbeddingDimension
