import HonestEmbeddingDimension.ParameterJetValues
import HonestEmbeddingDimension.TripleJets

set_option maxHeartbeats 1000000

namespace HonestEmbeddingDimension

noncomputable def fourBasis (Y Z W : PowerSeries ℂ) : Fin 4 → PowerSeries ℂ := ![1,Y,Z,W]
noncomputable def fiveBasis (Y Z W : PowerSeries ℂ) : Fin 5 → PowerSeries ℂ := ![1,Y,Z,Y*Z,W]
noncomputable def powerBasis (Y Z : PowerSeries ℂ) : Fin 4 → PowerSeries ℂ := ![1,Y,Y^2,Z]

theorem four_basis_multiplication {m N : ℕ} (hm : m ≠ 0) (Y Z W : PowerSeries ℂ)
    (hYY : InParameterJetSpan m hm (fourBasis Y Z W) N (Y*Y))
    (hYZ : InParameterJetSpan m hm (fourBasis Y Z W) N (Y*Z))
    (hYW : (N : ℕ∞) ≤ (Y*W).order) (hZZ : (N : ℕ∞) ≤ (Z*Z).order)
    (hZW : (N : ℕ∞) ≤ (Z*W).order) :
    ∀ i j, InParameterJetSpan m hm (fourBasis Y Z W) N
      (fourBasis Y Z W j * tripleCoordinates m Y Z i) := by
  intro i j
  fin_cases i
  · have h := (parameterJetSpan_basis (N := N) hm (fourBasis Y Z W) j).parameter_mul PowerSeries.X
    simpa [fourBasis,tripleCoordinates,PowerSeries.expand_X,mul_comm] using h
  · fin_cases j
    · change InParameterJetSpan m hm (fourBasis Y Z W) N (1*Y)
      simpa [fourBasis,tripleCoordinates,one_mul] using parameterJetSpan_basis (N := N) hm (fourBasis Y Z W) 1
    · exact hYY
    · simpa [fourBasis,tripleCoordinates,mul_comm] using hYZ
    · apply parameterJetSpan_of_order_ge
      simpa [fourBasis,tripleCoordinates,mul_comm] using hYW
  · fin_cases j
    · change InParameterJetSpan m hm (fourBasis Y Z W) N (1*Z)
      simpa [fourBasis,tripleCoordinates,one_mul] using parameterJetSpan_basis (N := N) hm (fourBasis Y Z W) 2
    · exact hYZ
    · exact parameterJetSpan_of_order_ge hm _ _ hZZ
    · apply parameterJetSpan_of_order_ge
      simpa [fourBasis,tripleCoordinates,mul_comm] using hZW

theorem five_basis_multiplication {m N : ℕ} (hm : m ≠ 0) (Y Z W : PowerSeries ℂ)
    (hYY : InParameterJetSpan m hm (fiveBasis Y Z W) N (Y*Y))
    (hYYZ : (N : ℕ∞) ≤ ((Y*Z)*Y).order) (hYW : (N : ℕ∞) ≤ (Y*W).order)
    (hZZ : (N : ℕ∞) ≤ (Z*Z).order) (hYZZ : (N : ℕ∞) ≤ ((Y*Z)*Z).order)
    (hZW : (N : ℕ∞) ≤ (Z*W).order) :
    ∀ i j, InParameterJetSpan m hm (fiveBasis Y Z W) N
      (fiveBasis Y Z W j * tripleCoordinates m Y Z i) := by
  intro i j
  fin_cases i
  · have h := (parameterJetSpan_basis (N := N) hm (fiveBasis Y Z W) j).parameter_mul PowerSeries.X
    simpa [fiveBasis,tripleCoordinates,PowerSeries.expand_X,mul_comm] using h
  · fin_cases j
    · change InParameterJetSpan m hm (fiveBasis Y Z W) N (1*Y)
      simpa [fiveBasis,tripleCoordinates,one_mul] using parameterJetSpan_basis (N := N) hm (fiveBasis Y Z W) 1
    · exact hYY
    · simpa [fiveBasis,tripleCoordinates,mul_comm] using parameterJetSpan_basis (N := N) hm (fiveBasis Y Z W) 3
    · exact parameterJetSpan_of_order_ge hm _ _ hYYZ
    · apply parameterJetSpan_of_order_ge
      simpa [fiveBasis,tripleCoordinates,mul_comm] using hYW
  · fin_cases j
    · change InParameterJetSpan m hm (fiveBasis Y Z W) N (1*Z)
      simpa [fiveBasis,tripleCoordinates,one_mul] using parameterJetSpan_basis (N := N) hm (fiveBasis Y Z W) 2
    · exact parameterJetSpan_basis (N := N) hm (fiveBasis Y Z W) 3
    · exact parameterJetSpan_of_order_ge hm _ _ hZZ
    · exact parameterJetSpan_of_order_ge hm _ _ hYZZ
    · apply parameterJetSpan_of_order_ge
      simpa [fiveBasis,tripleCoordinates,mul_comm] using hZW

theorem power_basis_multiplication {m N : ℕ} (hm : m ≠ 0) (Y Z : PowerSeries ℂ)
    (hYYY : InParameterJetSpan m hm (powerBasis Y Z) N (Y^3))
    (hYZ : InParameterJetSpan m hm (powerBasis Y Z) N (Y*Z))
    (hYYZ : (N : ℕ∞) ≤ (Y^2*Z).order) (hZZ : (N : ℕ∞) ≤ (Z*Z).order) :
    ∀ i j, InParameterJetSpan m hm (powerBasis Y Z) N
      (powerBasis Y Z j * tripleCoordinates m Y Z i) := by
  intro i j
  fin_cases i
  · have h := (parameterJetSpan_basis (N := N) hm (powerBasis Y Z) j).parameter_mul PowerSeries.X
    simpa [powerBasis,tripleCoordinates,PowerSeries.expand_X,mul_comm] using h
  · fin_cases j
    · change InParameterJetSpan m hm (powerBasis Y Z) N (1*Y)
      simpa [powerBasis,tripleCoordinates,one_mul] using parameterJetSpan_basis (N := N) hm (powerBasis Y Z) 1
    · simpa [powerBasis,tripleCoordinates,pow_two] using parameterJetSpan_basis (N := N) hm (powerBasis Y Z) 2
    · simpa [powerBasis,tripleCoordinates,pow_succ] using hYYY
    · simpa [powerBasis,tripleCoordinates,mul_comm] using hYZ
  · fin_cases j
    · change InParameterJetSpan m hm (powerBasis Y Z) N (1*Z)
      simpa [powerBasis,tripleCoordinates,one_mul] using parameterJetSpan_basis (N := N) hm (powerBasis Y Z) 3
    · exact hYZ
    · exact parameterJetSpan_of_order_ge hm _ _ hYYZ
    · exact parameterJetSpan_of_order_ge hm _ _ hZZ

end HonestEmbeddingDimension
