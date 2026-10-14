import HonestEmbeddingDimension.GeometricRealization

namespace HonestEmbeddingDimension

/-- Every multiplication entry for the rational residue-three realization is checked. -/
theorem geometric_basis_multiplication (m a b c δ u v N : ℕ) (hm : m ≠ 0) (hδ : 0 < δ)
    (hu : m*u+b=2*a) (hc : 2*a+δ=c) (hv : m*v+c=a+b)
    (hZZ : N ≤ 2*b) (hYW : N ≤ a+c) (hZW : N ≤ b+c) :
    ∀ i j, InParameterJetSpan m hm (geometricBasis a b c δ) N
      (geometricBasis a b c δ j * tripleCoordinates m (PowerSeries.X^a) (PowerSeries.X^b*geometricUnit δ) i) := by
  let B := geometricBasis a b c δ
  have hY2 : InParameterJetSpan m hm B N ((PowerSeries.X^a)^2) := by
    have h := ((parameterJetSpan_basis (N := N) hm B 2).parameter_mul (PowerSeries.X^u)).add
      (parameterJetSpan_basis (N := N) hm B 3)
    have he := geometric_first_cancellation m a b c δ u hδ hu hc
    have heq : (PowerSeries.X^m)^u*(PowerSeries.X^b*geometricUnit δ)+
        (-PowerSeries.X^c*geometricUnit δ) = (PowerSeries.X^a)^2 := by
      linear_combination -he
    change InParameterJetSpan m hm B N
      (PowerSeries.expand m hm (PowerSeries.X^u)*(PowerSeries.X^b*geometricUnit δ)+
        (-PowerSeries.X^c*geometricUnit δ)) at h
    rwa [map_pow,PowerSeries.expand_X,heq] at h
  have hYZ : InParameterJetSpan m hm B N
      (PowerSeries.X^a*(PowerSeries.X^b*geometricUnit δ)) := by
    have h := (parameterJetSpan_basis (N := N) hm B 3).parameter_mul (-(PowerSeries.X^v))
    have he := geometric_second_cancellation m a b c δ v hv
    have heq : -((PowerSeries.X^m)^v)*(-PowerSeries.X^c*geometricUnit δ) =
        PowerSeries.X^a*(PowerSeries.X^b*geometricUnit δ) := by linear_combination -he
    change InParameterJetSpan m hm B N
      (PowerSeries.expand m hm (-(PowerSeries.X^v))*(-PowerSeries.X^c*geometricUnit δ)) at h
    rwa [map_neg,map_pow,PowerSeries.expand_X,heq] at h
  intro i j
  fin_cases i
  · change InParameterJetSpan m hm B N (B j*PowerSeries.X^m)
    have h := (parameterJetSpan_basis (N := N) hm B j).parameter_mul PowerSeries.X
    simpa only [PowerSeries.expand_X,mul_comm] using h
  · fin_cases j
    · change InParameterJetSpan m hm B N (1*B 1)
      simpa only [one_mul] using parameterJetSpan_basis (N := N) hm B 1
    · change InParameterJetSpan m hm B N (PowerSeries.X^a*PowerSeries.X^a)
      simpa only [pow_two] using hY2
    · change InParameterJetSpan m hm B N ((PowerSeries.X^b*geometricUnit δ)*PowerSeries.X^a)
      simpa only [mul_comm] using hYZ
    · apply parameterJetSpan_of_order_ge
      change (N : ℕ∞) ≤ ((-PowerSeries.X^c*geometricUnit δ)*PowerSeries.X^a).order
      simp only [PowerSeries.order_mul,PowerSeries.order_neg,PowerSeries.order_pow,PowerSeries.order_X,
        order_geometricUnit δ hδ,nsmul_eq_mul,mul_one,add_zero]
      exact_mod_cast (show N ≤ c+a by omega)
  · fin_cases j
    · change InParameterJetSpan m hm B N (1*B 2)
      simpa only [one_mul] using parameterJetSpan_basis (N := N) hm B 2
    · exact hYZ
    · apply parameterJetSpan_of_order_ge
      change (N : ℕ∞) ≤ ((PowerSeries.X^b*geometricUnit δ)*(PowerSeries.X^b*geometricUnit δ)).order
      simp only [PowerSeries.order_mul,PowerSeries.order_pow,PowerSeries.order_X,
        order_geometricUnit δ hδ,nsmul_eq_mul,mul_one,add_zero]
      exact_mod_cast (show N ≤ b+b by omega)
    · apply parameterJetSpan_of_order_ge
      change (N : ℕ∞) ≤ ((-PowerSeries.X^c*geometricUnit δ)*(PowerSeries.X^b*geometricUnit δ)).order
      simp only [PowerSeries.order_mul,PowerSeries.order_neg,PowerSeries.order_pow,PowerSeries.order_X,
        order_geometricUnit δ hδ,nsmul_eq_mul,mul_one,add_zero]
      exact_mod_cast (show N ≤ c+b by omega)

end HonestEmbeddingDimension
