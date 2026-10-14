import HonestEmbeddingDimension.GeometricValues
import HonestEmbeddingDimension.BasisCertificates

namespace HonestEmbeddingDimension

noncomputable def doubleGeometricZ (b δ ε : ℕ) : PowerSeries ℂ :=
  PowerSeries.X^b*(1+PowerSeries.X^(δ+ε))*geometricUnit δ
noncomputable def doubleGeometricW (c δ ε : ℕ) : PowerSeries ℂ :=
  -PowerSeries.X^c*(1+PowerSeries.X^ε)*geometricUnit δ

theorem order_one_add_X_pow (n : ℕ) (hn : 0 < n) :
    (1+(PowerSeries.X : PowerSeries ℂ)^n).order = 0 := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · simp [PowerSeries.coeff_zero_eq_constantCoeff,Nat.ne_of_gt hn]
  · intro i hi; omega

theorem order_doubleGeometricZ (b δ ε : ℕ) (hδ : 0 < δ) :
    (doubleGeometricZ b δ ε).order = b := by
  simp [doubleGeometricZ,PowerSeries.order_mul,PowerSeries.order_pow,nsmul_eq_mul,
    order_one_add_X_pow (δ+ε) (by omega),order_geometricUnit δ hδ]

theorem order_doubleGeometricW (c δ ε : ℕ) (hδ : 0 < δ) (hε : 0 < ε) :
    (doubleGeometricW c δ ε).order = c := by
  simp [doubleGeometricW,PowerSeries.order_mul,PowerSeries.order_pow,PowerSeries.order_neg,nsmul_eq_mul,
    order_one_add_X_pow ε hε,order_geometricUnit δ hδ]

/-- The first cancellation in the five-generator rational realization. -/
theorem double_geometric_first_cancellation (m a b c δ ε u : ℕ) (hδ : 0 < δ)
    (hu : m*u+b=2*a) (hc : 2*a+δ=c) :
    (PowerSeries.X^a)^2-(PowerSeries.X^m)^u*doubleGeometricZ b δ ε =
      doubleGeometricW c δ ε := by
  have hU := geometricUnit_identity δ hδ
  have hp : (PowerSeries.X^m)^u*PowerSeries.X^b = (PowerSeries.X : PowerSeries ℂ)^(2*a) := by
    rw [← pow_mul,← pow_add,hu]
  unfold doubleGeometricZ doubleGeometricW
  rw [← mul_assoc,← mul_assoc,hp,← hc]
  rw [pow_add (PowerSeries.X : PowerSeries ℂ) (2*a) δ,
    pow_add (PowerSeries.X : PowerSeries ℂ) δ ε]
  have ha2 : (PowerSeries.X^a)^2 = (PowerSeries.X : PowerSeries ℂ)^(2*a) := by rw [← pow_mul,Nat.mul_comm]
  rw [ha2]
  linear_combination -(PowerSeries.X^(2*a))*hU

/-- The second cancellation gives the final generator as an exact monomial. -/
theorem double_geometric_second_cancellation (m a b c d δ ε v : ℕ) (hδ : 0 < δ)
    (hv : m*v+c=a+b) (hd : a+b+ε=d) :
    PowerSeries.X^a*doubleGeometricZ b δ ε+
      (PowerSeries.X^m)^v*doubleGeometricW c δ ε = -PowerSeries.X^d := by
  have hU := geometricUnit_identity δ hδ
  have hp : (PowerSeries.X^m)^v*PowerSeries.X^c = (PowerSeries.X : PowerSeries ℂ)^(a+b) := by
    rw [← pow_mul,← pow_add,hv]
  unfold doubleGeometricZ doubleGeometricW
  simp only [mul_neg,← mul_assoc]
  rw [hp,← pow_add (PowerSeries.X : PowerSeries ℂ) a b,← hd,
    pow_add (PowerSeries.X : PowerSeries ℂ) (a+b) ε,
    pow_add (PowerSeries.X : PowerSeries ℂ) δ ε]
  linear_combination -(PowerSeries.X^(a+b)*PowerSeries.X^ε)*hU

end HonestEmbeddingDimension
