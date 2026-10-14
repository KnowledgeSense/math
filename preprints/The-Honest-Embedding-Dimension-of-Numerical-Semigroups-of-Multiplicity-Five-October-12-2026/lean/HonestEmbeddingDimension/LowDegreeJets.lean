import HonestEmbeddingDimension.JetResidueBound

namespace HonestEmbeddingDimension

noncomputable def parameterCoordinates {d : ℕ} (m : ℕ) (f : Fin d → PowerSeries ℂ) :
    Fin (d+1) → PowerSeries ℂ := Fin.cons (PowerSeries.X^m) f

noncomputable def linearParameterBasis {d : ℕ} (f : Fin d → PowerSeries ℂ) :
    Fin (d+1) → PowerSeries ℂ := Fin.cons 1 f

/-- Below twice the first nonparameter order, only the constant and linear parameter-module terms survive. -/
theorem linear_basis_multiplication {d m a N : ℕ} (hm : m ≠ 0)
    (f : Fin d → PowerSeries ℂ) (hf : ∀ i, (a : ℕ∞) ≤ (f i).order) (hN : N ≤ 2*a) :
    ∀ i j, InParameterJetSpan m hm (linearParameterBasis f) N
      (linearParameterBasis f j * parameterCoordinates m f i) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    have h := (parameterJetSpan_basis (N := N) hm (linearParameterBasis f) j).parameter_mul PowerSeries.X
    simpa [parameterCoordinates,mul_comm] using h
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [linearParameterBasis,parameterCoordinates] using
        parameterJetSpan_basis (N := N) hm (linearParameterBasis f) i.succ
    · apply parameterJetSpan_of_order_ge
      change (N : ℕ∞) ≤ (f j*f i).order
      rw [PowerSeries.order_mul]
      exact le_trans (by exact_mod_cast (show N ≤ a+a by omega)) (add_le_add (hf j) (hf i))

theorem linear_polynomial_jet {d m a N : ℕ} (hm : m ≠ 0)
    (f : Fin d → PowerSeries ℂ) (hf : ∀ i, (a : ℕ∞) ≤ (f i).order) (hN : N ≤ 2*a)
    (P : MvPolynomial (Fin (d+1)) ℂ) :
    InParameterJetSpan m hm (linearParameterBasis f) N (MvPolynomial.aeval (parameterCoordinates m f) P) :=
  polynomial_jet_of_parameter_basis hm _ _ 0 rfl (linear_basis_multiplication hm f hf hN) P

/-- The low-order residue obstruction uses the actual ambient dimension. -/
theorem linear_low_residue_bound {d m a N p : ℕ} (hm : m ≠ 0)
    (f : Fin d → PowerSeries ℂ) (hf : ∀ i, (a : ℕ∞) ≤ (f i).order) (hN : N ≤ 2*a)
    (w : Fin p → ℕ) (hw : ∀ i, w i < N)
    (hres : Function.Injective (fun i => w i % m))
    (hv : ∀ i, w i ∈ polynomialValues (parameterCoordinates m f)) : p ≤ d+1 :=
  low_value_residue_count hm _ _ (linear_polynomial_jet hm f hf hN) w hw hres hv

end HonestEmbeddingDimension
