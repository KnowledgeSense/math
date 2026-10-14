import HonestEmbeddingDimension.ParameterJetSpan

namespace HonestEmbeddingDimension

/-- A checked multiplication table and a conductor bound rule out every extra polynomial value. -/
theorem polynomialValues_subset_of_parameter_basis {d q m N : ℕ} (hm : m ≠ 0)
    (S : AddSubmonoid ℕ) (hmS : m ∈ S)
    (f : Fin d → PowerSeries ℂ) (B : Fin q → PowerSeries ℂ) (w : Fin q → ℕ)
    (hw : ∀ i, (B i).order = w i) (hwS : ∀ i, w i ∈ S)
    (hres : Function.Injective (fun i => w i % m))
    (htail : ∀ n, N ≤ n → n ∈ S)
    (e : Fin q) (he : B e = 1)
    (hmul : ∀ i j, InParameterJetSpan m hm B N (B j*f i)) :
    polynomialValues f ⊆ S := by
  intro n hn
  by_cases hN : n < N
  · obtain ⟨P,hP⟩ := hn
    obtain ⟨u,hu⟩ := polynomial_jet_of_parameter_basis hm f B e he hmul P
    have ho := (order_eq_of_jet_eq hu hN).mp hP
    obtain ⟨i,_,k,hk⟩ := order_of_parameter_span Finset.univ m hm u B w
      (by intro i _; exact hw i)
      (by intro i _ j _ hij heq; exact hij (hres heq)) n ho
    rw [hk]
    apply S.add_mem _ (hwS i)
    simpa [nsmul_eq_mul,Nat.mul_comm] using S.nsmul_mem hmS k
  · exact htail n (Nat.le_of_not_gt hN)

/-- The same finite multiplication certificate controls the full infinite formal algebra. -/
theorem formalValues_subset_of_parameter_basis {d q m N : ℕ} (hm : m ≠ 0)
    (S : AddSubmonoid ℕ) (hmS : m ∈ S)
    (f : Fin d → PowerSeries ℂ) (hf0 : ∀ i, (f i).constantCoeff = 0)
    (B : Fin q → PowerSeries ℂ) (w : Fin q → ℕ)
    (hw : ∀ i, (B i).order = w i) (hwS : ∀ i, w i ∈ S)
    (hres : Function.Injective (fun i => w i % m))
    (htail : ∀ n, N ≤ n → n ∈ S)
    (e : Fin q) (he : B e = 1)
    (hmul : ∀ i j, InParameterJetSpan m hm B N (B j*f i)) :
    formalValues f ⊆ S := by
  rw [formalValues_eq_polynomialValues f hf0]
  exact polynomialValues_subset_of_parameter_basis hm S hmS f B w hw hwS hres htail e he hmul

theorem formalValues_eq_of_parameter_basis {d q m N : ℕ} (hm : m ≠ 0)
    (S : AddSubmonoid ℕ) (hmS : m ∈ S)
    (f : Fin d → PowerSeries ℂ) (hf0 : ∀ i, (f i).constantCoeff = 0)
    (B : Fin q → PowerSeries ℂ) (w : Fin q → ℕ)
    (hw : ∀ i, (B i).order = w i) (hwS : ∀ i, w i ∈ S)
    (hres : Function.Injective (fun i => w i % m))
    (htail : ∀ n, N ≤ n → n ∈ S) (e : Fin q) (he : B e = 1)
    (hmul : ∀ i j, InParameterJetSpan m hm B N (B j*f i))
    (G : Set ℕ) (hgens : AddSubmonoid.closure G = S)
    (hG : G ⊆ formalValues f) : formalValues f = S := by
  apply Set.Subset.antisymm
  · exact formalValues_subset_of_parameter_basis hm S hmS f hf0 B w hw hwS hres htail e he hmul
  · change S ≤ formalValueSubmonoid f hf0
    rw [← hgens]
    exact AddSubmonoid.closure_le.mpr hG

end HonestEmbeddingDimension
