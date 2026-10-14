import HonestEmbeddingDimension.DoubleGeometricRealization

namespace HonestEmbeddingDimension

theorem double_geometric_basis_multiplication (m a b c d δ ε u v : ℕ)
    (hm : m ≠ 0) (hδ : 0 < δ) (hε : 0 < ε)
    (hu : m*u+b=2*a) (hc : 2*a+δ=c) (hv : m*v+c=a+b) (hd : a+b+ε=d)
    (hZZ : d ≤ 2*b) (hYW : d ≤ a+c) (hZW : d ≤ b+c) :
    ∀ i j, InParameterJetSpan m hm
      (fourBasis (PowerSeries.X^a) (doubleGeometricZ b δ ε) (doubleGeometricW c δ ε)) d
      (fourBasis (PowerSeries.X^a) (doubleGeometricZ b δ ε) (doubleGeometricW c δ ε) j *
        tripleCoordinates m (PowerSeries.X^a) (doubleGeometricZ b δ ε) i) := by
  let Y : PowerSeries ℂ := PowerSeries.X^a
  let Z := doubleGeometricZ b δ ε
  let W := doubleGeometricW c δ ε
  let B := fourBasis Y Z W
  have hYY : InParameterJetSpan m hm B d (Y*Y) := by
    have h := ((parameterJetSpan_basis (N := d) hm B 2).parameter_mul (PowerSeries.X^u)).add
      (parameterJetSpan_basis (N := d) hm B 3)
    change InParameterJetSpan m hm B d (PowerSeries.expand m hm (PowerSeries.X^u)*Z+W) at h
    rw [map_pow,PowerSeries.expand_X] at h
    have he := double_geometric_first_cancellation m a b c δ ε u hδ hu hc
    have heq : (PowerSeries.X^m)^u*Z+W = Y*Y := by
      change (PowerSeries.X^m)^u*doubleGeometricZ b δ ε+doubleGeometricW c δ ε = (PowerSeries.X^a)*(PowerSeries.X^a)
      linear_combination -he
    rwa [heq] at h
  have hYZ : InParameterJetSpan m hm B d (Y*Z) := by
    have h := (parameterJetSpan_basis (N := d) hm B 3).parameter_mul (-(PowerSeries.X^v))
    have hz : InParameterJetSpan m hm B d (-PowerSeries.X^d) := by
      apply parameterJetSpan_of_order_ge
      simp [PowerSeries.order_neg,PowerSeries.order_pow,nsmul_eq_mul]
    have hs := h.add hz
    change InParameterJetSpan m hm B d
      (PowerSeries.expand m hm (-(PowerSeries.X^v))*W+(-PowerSeries.X^d)) at hs
    rw [map_neg,map_pow,PowerSeries.expand_X] at hs
    have he := double_geometric_second_cancellation m a b c d δ ε v hδ hv hd
    have heq : -((PowerSeries.X^m)^v)*W+(-PowerSeries.X^d)=Y*Z := by
      change -((PowerSeries.X^m)^v)*doubleGeometricW c δ ε+(-PowerSeries.X^d)=PowerSeries.X^a*doubleGeometricZ b δ ε
      linear_combination -he
    rwa [heq] at hs
  apply four_basis_multiplication hm Y Z W hYY hYZ
  · change (d : ℕ∞) ≤ (PowerSeries.X^a*doubleGeometricW c δ ε).order
    simp only [PowerSeries.order_mul,PowerSeries.order_pow,PowerSeries.order_X,nsmul_eq_mul,mul_one,
      order_doubleGeometricW c δ ε hδ hε]
    exact_mod_cast hYW
  · change (d : ℕ∞) ≤ (doubleGeometricZ b δ ε*doubleGeometricZ b δ ε).order
    rw [PowerSeries.order_mul,order_doubleGeometricZ b δ ε hδ]
    exact_mod_cast (show d ≤ b+b by omega)
  · change (d : ℕ∞) ≤ (doubleGeometricZ b δ ε*doubleGeometricW c δ ε).order
    rw [PowerSeries.order_mul,order_doubleGeometricZ b δ ε hδ,order_doubleGeometricW c δ ε hδ hε]
    exact_mod_cast hZW

end HonestEmbeddingDimension
