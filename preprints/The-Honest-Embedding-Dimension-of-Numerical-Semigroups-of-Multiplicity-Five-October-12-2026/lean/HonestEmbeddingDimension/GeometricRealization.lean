import HonestEmbeddingDimension.RationalGerms
import HonestEmbeddingDimension.ParameterJetValues
import HonestEmbeddingDimension.TripleJets

namespace HonestEmbeddingDimension

noncomputable def geometricUnit (δ : ℕ) : PowerSeries ℂ := (1-PowerSeries.X^δ)⁻¹

@[simp] theorem constantCoeff_geometricUnit (δ : ℕ) (hδ : 0 < δ) :
    (geometricUnit δ).constantCoeff = 1 := by
  simp [geometricUnit,PowerSeries.constantCoeff_inv,Nat.ne_of_gt hδ]

theorem order_geometricUnit (δ : ℕ) (hδ : 0 < δ) : (geometricUnit δ).order = 0 := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · simpa only [PowerSeries.coeff_zero_eq_constantCoeff,constantCoeff_geometricUnit δ hδ] using (one_ne_zero : (1 : ℂ) ≠ 0)
  · intro i hi; omega

theorem geometricUnit_identity (δ : ℕ) (hδ : 0 < δ) :
    (1-PowerSeries.X^δ)*geometricUnit δ = 1 := by
  apply PowerSeries.mul_inv_cancel
  simp [Nat.ne_of_gt hδ]

/-- The first exact cancellation in the rational four-generator construction. -/
theorem geometric_first_cancellation (m a b c δ u : ℕ) (hδ : 0 < δ)
    (hu : m*u+b=2*a) (hc : 2*a+δ=c) :
    (PowerSeries.X^a)^2-(PowerSeries.X^m)^u*(PowerSeries.X^b*geometricUnit δ) =
      -PowerSeries.X^c*geometricUnit δ := by
  have hU := geometricUnit_identity δ hδ
  calc
    _ = PowerSeries.X^(2*a)-PowerSeries.X^(m*u+b)*geometricUnit δ := by
      rw [← pow_mul,← pow_mul,← mul_assoc,← pow_add]
      simp [Nat.mul_comm]
    _ = PowerSeries.X^(2*a)-PowerSeries.X^(2*a)*geometricUnit δ := by rw [hu]
    _ = -(PowerSeries.X^(2*a)*PowerSeries.X^δ)*geometricUnit δ := by
      linear_combination -(PowerSeries.X^(2*a))*hU
    _ = _ := by rw [← pow_add,hc]

/-- The second exact cancellation, responsible for the special residue-three case. -/
theorem geometric_second_cancellation (m a b c δ v : ℕ) (hv : m*v+c=a+b) :
    PowerSeries.X^a*(PowerSeries.X^b*geometricUnit δ)+
      (PowerSeries.X^m)^v*(-PowerSeries.X^c*geometricUnit δ) = 0 := by
  rw [← pow_mul]
  simp only [mul_neg,← mul_assoc,← pow_add]
  rw [hv]
  ring

noncomputable def geometricBasis (a b c δ : ℕ) : Fin 4 → PowerSeries ℂ :=
  ![1,PowerSeries.X^a,PowerSeries.X^b*geometricUnit δ,-PowerSeries.X^c*geometricUnit δ]

theorem order_geometricBasis (a b c δ : ℕ) (hδ : 0 < δ) (i : Fin 4) :
    (geometricBasis a b c δ i).order = (![0,a,b,c] : Fin 4 → ℕ) i := by
  fin_cases i <;> simp [geometricBasis,PowerSeries.order_mul,PowerSeries.order_pow,
    PowerSeries.order_neg,order_geometricUnit δ hδ,nsmul_eq_mul]

end HonestEmbeddingDimension
