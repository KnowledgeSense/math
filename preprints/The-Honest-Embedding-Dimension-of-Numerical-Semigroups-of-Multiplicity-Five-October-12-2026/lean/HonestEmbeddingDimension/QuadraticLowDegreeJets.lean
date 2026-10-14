import HonestEmbeddingDimension.LowDegreeJets
import HonestEmbeddingDimension.BasisCertificates

namespace HonestEmbeddingDimension

/-- The actual four-term basis below `a+b`, including the collision-prone square. -/
theorem quadratic_low_polynomial_jet (m a b : ℕ) (hm : m ≠ 0)
    (Y Z : PowerSeries ℂ) (hY : Y.order=a) (hZ : Z.order=b)
    (hab : a ≤ b) (hba : b ≤ 2*a) (P : MvPolynomial (Fin 3) ℂ) :
    InParameterJetSpan m hm (powerBasis Y Z) (a+b)
      (MvPolynomial.aeval (tripleCoordinates m Y Z) P) := by
  apply polynomial_jet_of_parameter_basis hm _ _ 0 rfl _ P
  apply power_basis_multiplication hm Y Z
  · apply parameterJetSpan_of_order_ge
    rw [PowerSeries.order_pow,hY,nsmul_eq_mul]
    exact_mod_cast (show a+b ≤ 3*a by omega)
  · apply parameterJetSpan_of_order_ge
    rw [PowerSeries.order_mul,hY,hZ]
    norm_cast
  · rw [PowerSeries.order_mul,PowerSeries.order_pow,hY,hZ,nsmul_eq_mul]
    exact_mod_cast (show a+b ≤ 2*a+b by omega)
  · rw [PowerSeries.order_mul,hZ]
    exact_mod_cast (show a+b ≤ b+b by omega)

/-- Five different low residues cannot occur in the four-term quadratic jet span. -/
theorem quadratic_low_residue_bound (m a b p : ℕ) (hm : m ≠ 0)
    (Y Z : PowerSeries ℂ) (hY : Y.order=a) (hZ : Z.order=b)
    (hab : a ≤ b) (hba : b ≤ 2*a)
    (w : Fin p → ℕ) (hw : ∀ i, w i < a+b)
    (hres : Function.Injective (fun i => w i % m))
    (hv : ∀ i, w i ∈ polynomialValues (tripleCoordinates m Y Z)) : p ≤ 4 :=
  low_value_residue_count hm _ _ (quadratic_low_polynomial_jet m a b hm Y Z hY hZ hab hba)
    w hw hres hv

end HonestEmbeddingDimension
