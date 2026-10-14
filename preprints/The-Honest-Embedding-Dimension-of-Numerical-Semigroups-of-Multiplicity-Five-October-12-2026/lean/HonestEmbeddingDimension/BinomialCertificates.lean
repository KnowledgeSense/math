import HonestEmbeddingDimension.BinomialRealization

namespace HonestEmbeddingDimension

theorem binomial_basis_4B (m a b c δ u N : ℕ) (hm : m ≠ 0) (hδ : 0 < δ)
    (hu : m*u+b=2*a) (hc : 2*a+δ=c)
    (hYYZ : N ≤ 2*a+b) (hYW : N ≤ a+c) (hZZ : N ≤ 2*b)
    (hYZZ : N ≤ a+2*b) (hZW : N ≤ b+c) :
    ∀ i j, InParameterJetSpan m hm (fiveBasis (PowerSeries.X^a) (binomialCoordinate b δ) (-PowerSeries.X^c)) N
      (fiveBasis (PowerSeries.X^a) (binomialCoordinate b δ) (-PowerSeries.X^c) j *
        tripleCoordinates m (PowerSeries.X^a) (binomialCoordinate b δ) i) := by
  let Y : PowerSeries ℂ := PowerSeries.X^a
  let Z := binomialCoordinate b δ
  let W : PowerSeries ℂ := -PowerSeries.X^c
  let B := fiveBasis Y Z W
  have hYY : InParameterJetSpan m hm B N (Y*Y) := by
    have h := ((parameterJetSpan_basis (N := N) hm B 2).parameter_mul (PowerSeries.X^u)).add
      (parameterJetSpan_basis (N := N) hm B 4)
    change InParameterJetSpan m hm B N (PowerSeries.expand m hm (PowerSeries.X^u)*Z+W) at h
    rw [map_pow,PowerSeries.expand_X] at h
    have he := binomial_first_cancellation m a b c δ u 2 hu hc
    have heq : (PowerSeries.X^m)^u*Z+W=Y*Y := by
      change (PowerSeries.X^m)^u*binomialCoordinate b δ+(-PowerSeries.X^c)=(PowerSeries.X^a)*(PowerSeries.X^a)
      linear_combination -he
    rwa [heq] at h
  have hY : Y.order = a := by simp [Y,PowerSeries.order_pow,nsmul_eq_mul]
  have hZ : Z.order = b := order_binomialCoordinate b δ hδ
  have hW : W.order = c := by simp [W,PowerSeries.order_neg,PowerSeries.order_pow,nsmul_eq_mul]
  apply five_basis_multiplication hm Y Z W hYY
  · rw [PowerSeries.order_mul,PowerSeries.order_mul,hY,hZ]
    exact_mod_cast (show N ≤ (a+b)+a by omega)
  · rw [PowerSeries.order_mul,hY,hW]; exact_mod_cast hYW
  · rw [PowerSeries.order_mul,hZ]; exact_mod_cast (show N ≤ b+b by omega)
  · rw [PowerSeries.order_mul,PowerSeries.order_mul,hY,hZ]
    exact_mod_cast (show N ≤ (a+b)+b by omega)
  · rw [PowerSeries.order_mul,hZ,hW]; exact_mod_cast hZW

theorem binomial_basis_4C (m a b c δ u : ℕ) (hm : m ≠ 0) (hδ : 0 < δ)
    (hu : m*u+b=3*a) (hc : 3*a+δ=c)
    (hYZ : c ≤ a+b) (hYYZ : c ≤ 2*a+b) (hZZ : c ≤ 2*b) :
    ∀ i j, InParameterJetSpan m hm (powerBasis (PowerSeries.X^a) (binomialCoordinate b δ)) c
      (powerBasis (PowerSeries.X^a) (binomialCoordinate b δ) j *
        tripleCoordinates m (PowerSeries.X^a) (binomialCoordinate b δ) i) := by
  let Y : PowerSeries ℂ := PowerSeries.X^a
  let Z := binomialCoordinate b δ
  let B := powerBasis Y Z
  have hY : Y.order = a := by simp [Y,PowerSeries.order_pow,nsmul_eq_mul]
  have hZ : Z.order = b := order_binomialCoordinate b δ hδ
  have hYYY : InParameterJetSpan m hm B c (Y^3) := by
    have h := (parameterJetSpan_basis (N := c) hm B 3).parameter_mul (PowerSeries.X^u)
    have hz : InParameterJetSpan m hm B c (-PowerSeries.X^c) := by
      apply parameterJetSpan_of_order_ge
      simp [PowerSeries.order_neg,PowerSeries.order_pow,nsmul_eq_mul]
    have hs := h.add hz
    change InParameterJetSpan m hm B c (PowerSeries.expand m hm (PowerSeries.X^u)*Z+(-PowerSeries.X^c)) at hs
    rw [map_pow,PowerSeries.expand_X] at hs
    have he := binomial_first_cancellation m a b c δ u 3 hu hc
    have heq : (PowerSeries.X^m)^u*Z+(-PowerSeries.X^c)=Y^3 := by
      change (PowerSeries.X^m)^u*binomialCoordinate b δ+(-PowerSeries.X^c)=(PowerSeries.X^a)^3
      linear_combination -he
    rwa [heq] at hs
  apply power_basis_multiplication hm Y Z hYYY
  · apply parameterJetSpan_of_order_ge
    rw [PowerSeries.order_mul,hY,hZ]; exact_mod_cast hYZ
  · rw [PowerSeries.order_mul,PowerSeries.order_pow,hY,hZ,nsmul_eq_mul]
    exact_mod_cast hYYZ
  · rw [PowerSeries.order_mul,hZ]; exact_mod_cast (show c ≤ b+b by omega)

theorem binomial_basis_4D (m a b c δ u : ℕ) (hm : m ≠ 0) (hδ : 0 < δ)
    (hu : m*u=a+b) (hc : a+b+δ=c)
    (hYYY : c ≤ 3*a) (hYYZ : c ≤ 2*a+b) (hZZ : c ≤ 2*b) :
    ∀ i j, InParameterJetSpan m hm (powerBasis (PowerSeries.X^a) (binomialCoordinate b δ)) c
      (powerBasis (PowerSeries.X^a) (binomialCoordinate b δ) j *
        tripleCoordinates m (PowerSeries.X^a) (binomialCoordinate b δ) i) := by
  let Y : PowerSeries ℂ := PowerSeries.X^a
  let Z := binomialCoordinate b δ
  let B := powerBasis Y Z
  have hY : Y.order = a := by simp [Y,PowerSeries.order_pow,nsmul_eq_mul]
  have hZ : Z.order = b := order_binomialCoordinate b δ hδ
  have hYZ : InParameterJetSpan m hm B c (Y*Z) := by
    have h := (parameterJetSpan_basis (N := c) hm B 0).parameter_mul (PowerSeries.X^u)
    have hz : InParameterJetSpan m hm B c (PowerSeries.X^c) := by
      apply parameterJetSpan_of_order_ge
      simp [PowerSeries.order_pow,nsmul_eq_mul]
    have hs := h.add hz
    change InParameterJetSpan m hm B c (PowerSeries.expand m hm (PowerSeries.X^u)*1+PowerSeries.X^c) at hs
    rw [map_pow,PowerSeries.expand_X,mul_one] at hs
    have he := binomial_product_cancellation m a b c δ u hu hc
    have heq : (PowerSeries.X^m)^u+PowerSeries.X^c=Y*Z := by
      change (PowerSeries.X^m)^u+PowerSeries.X^c=PowerSeries.X^a*binomialCoordinate b δ
      linear_combination -he
    rwa [heq] at hs
  have hYYYspan : InParameterJetSpan m hm B c (Y^3) := by
    apply parameterJetSpan_of_order_ge
    rw [PowerSeries.order_pow,hY,nsmul_eq_mul]
    exact_mod_cast hYYY
  apply power_basis_multiplication hm Y Z hYYYspan hYZ
  · rw [PowerSeries.order_mul,PowerSeries.order_pow,hY,hZ,nsmul_eq_mul]
    exact_mod_cast hYYZ
  · rw [PowerSeries.order_mul,hZ]; exact_mod_cast (show c ≤ b+b by omega)

end HonestEmbeddingDimension
