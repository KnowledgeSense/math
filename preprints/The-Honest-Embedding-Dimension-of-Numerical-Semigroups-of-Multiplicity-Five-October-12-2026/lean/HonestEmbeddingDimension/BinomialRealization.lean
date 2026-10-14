import HonestEmbeddingDimension.DoubleGeometricRealization

namespace HonestEmbeddingDimension

noncomputable def binomialCoordinate (b δ : ℕ) : PowerSeries ℂ :=
  PowerSeries.X^b*(1+PowerSeries.X^δ)

theorem order_binomialCoordinate (b δ : ℕ) (hδ : 0 < δ) :
    (binomialCoordinate b δ).order = b := by
  simp [binomialCoordinate,PowerSeries.order_mul,PowerSeries.order_pow,nsmul_eq_mul,
    order_one_add_X_pow δ hδ]

/-- The exact binomial cancellation used in cases 4B and 4C. -/
theorem binomial_first_cancellation (m a b c δ u q : ℕ)
    (hu : m*u+b=q*a) (hc : q*a+δ=c) :
    (PowerSeries.X^a)^q-(PowerSeries.X^m)^u*binomialCoordinate b δ = -PowerSeries.X^c := by
  unfold binomialCoordinate
  rw [← pow_mul,← pow_mul,← mul_assoc,← pow_add,hu,← hc,pow_add]
  simp only [Nat.mul_comm a q]
  ring

/-- The exact binomial cancellation used in case 4D. -/
theorem binomial_product_cancellation (m a b c δ u : ℕ)
    (hu : m*u=a+b) (hc : a+b+δ=c) :
    PowerSeries.X^a*binomialCoordinate b δ-(PowerSeries.X^m)^u = PowerSeries.X^c := by
  unfold binomialCoordinate
  rw [← mul_assoc,← pow_add,← pow_mul,hu,← hc,pow_add]
  ring

theorem analyticAt_binomial (b δ : ℕ) :
    AnalyticAt ℂ (fun t : ℂ => t^b*(1+t^δ)) 0 :=
  (analyticAt_id.pow b).mul (analyticAt_const.add (analyticAt_id.pow δ))

theorem analyticTaylor_binomial (b δ : ℕ) :
    analyticTaylor (fun t : ℂ => t^b*(1+t^δ)) = binomialCoordinate b δ := by
  rw [analyticTaylor_mul (f := fun t : ℂ => t^b) (g := fun t => 1+t^δ)
    (analyticAt_id.pow b) (analyticAt_const.add (analyticAt_id.pow δ))]
  rw [analyticTaylor_add (f := fun _ : ℂ => 1) (g := fun t => t^δ) analyticAt_const (analyticAt_id.pow δ)]
  simp [analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id,binomialCoordinate]

end HonestEmbeddingDimension
