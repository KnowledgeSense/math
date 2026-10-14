import HonestEmbeddingDimension.CollisionNecessity
import HonestEmbeddingDimension.QuadraticLowDegreeJets
import HonestEmbeddingDimension.RemainingConstructionArithmetic

namespace HonestEmbeddingDimension

/-- Both strict inequalities in the five-generator criterion are forced by actual analytic realization. -/
theorem five_generator_bounds_necessary {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d)
    (hreal : AnalyticallyRealizes S 3) : 2*a<c ∧ a+b<d := by
  obtain ⟨ha,hmina,hb,hminb,_,_⟩ := h.normalization_data hm
  obtain ⟨h5,haGen,hbGen,hcGen,hdGen⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcd := h.c_lt_d
  obtain ⟨Y,Z,hY,hZ,hvalues⟩ := analytic_characteristic_triple hm (by omega) (by omega)
    (NumericalSemigroup.minimalGenerator_coprime_five hm haGen (by omega)).symm
    haGen.2.1 hbGen.2.1 ha hmina hb hminb hreal
  have hf0 : ∀ i, (tripleCoordinates 5 Y Z i).constantCoeff=0 := by
    intro i
    fin_cases i
    · simp [tripleCoordinates]
    · apply PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
      change (1 : ℕ∞) ≤ Y.order
      rw [hY]; exact_mod_cast (show 1 ≤ a by omega)
    · apply PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
      change (1 : ℕ∞) ≤ Z.order
      rw [hZ]; exact_mod_cast (show 1 ≤ b by omega)
  have hv5 : ∀ i : Fin 5, (![0,a,b,c,d] : Fin 5 → ℕ) i ∈
      polynomialValues (tripleCoordinates 5 Y Z) := by
    intro i
    rw [← formalValues_eq_polynomialValues _ hf0,hvalues]
    fin_cases i
    · exact S.monoid.zero_mem
    · exact haGen.2.1
    · exact hbGen.2.1
    · exact hcGen.2.1
    · exact hdGen.2.1
  have hcne : c ≠ 2*a := by
    intro he
    have hh := hcGen.2.2 a haGen.2.1 a haGen.2.1 (by omega)
    omega
  have hclower : 2*a<c := by
    by_contra hnot
    have hclt : c<2*a := by omega
    have he : parameterCoordinates 5 (![Y,Z] : Fin 2 → PowerSeries ℂ) = tripleCoordinates 5 Y Z := by
      funext i; fin_cases i <;> rfl
    have hf : ∀ i : Fin 2, (a : ℕ∞) ≤ ((![Y,Z] : Fin 2 → PowerSeries ℂ) i).order := by
      intro i
      fin_cases i
      · change (a : ℕ∞) ≤ Y.order; rw [hY]
      · change (a : ℕ∞) ≤ Z.order; rw [hZ]; exact_mod_cast hab.le
    have hh := linear_low_residue_bound (m := 5) (a := a) (N := 2*a) (by omega)
      (![Y,Z] : Fin 2 → PowerSeries ℂ) hf le_rfl (![0,a,b,c] : Fin 4 → ℕ)
      (by intro i; fin_cases i <;> dsimp <;> omega)
      (five_generator_first_four_residues_injective hm h) (by
        intro i
        rw [he]
        have heq : (![0,a,b,c,d] : Fin 5 → ℕ) i.castSucc = (![0,a,b,c] : Fin 4 → ℕ) i := by
          fin_cases i <;> rfl
        rw [← heq]
        exact hv5 i.castSucc)
    omega
  refine ⟨hclower,?_⟩
  obtain ⟨_,hb2⟩ := five_generator_second_of_first_bound hm h hclower
  have hdne : d ≠ a+b := by
    intro he
    have hh := hdGen.2.2 a haGen.2.1 b hbGen.2.1 he.symm
    omega
  by_contra hnot
  have hdlt : d<a+b := by omega
  have hh := quadratic_low_residue_bound 5 a b 5 (by omega) Y Z hY hZ hab.le hb2.le
    (![0,a,b,c,d] : Fin 5 → ℕ) (by intro i; fin_cases i <;> dsimp <;> omega)
    (five_generator_basis_residues_injective hm h) hv5
  omega

end HonestEmbeddingDimension
