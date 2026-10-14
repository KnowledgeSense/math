import HonestEmbeddingDimension.IntrinsicNormalForm
import HonestEmbeddingDimension.LowDegreeJets

namespace HonestEmbeddingDimension

/-- All nonparameter coordinates can simultaneously be raised to the first nonmultiple value. -/
theorem parameterized_normal_form {S : NumericalSemigroup} {a e : ℕ}
    (hm : HasMultiplicity S 5) (_ha0 : 0<a) (hav : a ∈ S.monoid) (ha : ¬5∣a)
    (hmina : ∀ n ∈ S.monoid, ¬5∣n → a≤n)
    (hreal : FormallyRealizes S (e+1)) :
    ∃ f : Fin e → PowerSeries ℂ, (∀ i, (a : ℕ∞) ≤ (f i).order) ∧
      polynomialValues (parameterCoordinates 5 f) = (S.monoid : Set ℕ) := by
  obtain ⟨F,hF0,hFS⟩ := hreal
  have hmem (n : ℕ) : n ∈ formalValues F ↔ n ∈ S.monoid := by rw [hFS]; rfl
  obtain ⟨i,g,hgi,hg0,hgv⟩ := normalize_minimum_coordinate F hF0 5 (by omega)
    ((hmem 5).mpr hm.2.1) (by intro n hn; exact hm.2.2 n ((hmem n).mp hn))
  have hgS : polynomialValues g = (S.monoid : Set ℕ) := by
    rw [← formalValues_eq_polynomialValues g hg0,hgv,hFS]
  have hgm (n : ℕ) : n ∈ polynomialValues g ↔ n ∈ S.monoid := by rw [hgS]; rfl
  have hs := partial_singleton_values g i 5 (by omega) hgi
  obtain ⟨h,he,hfix,horder,_,_,_⟩ := normalize_coordinate_outside_subalgebra g {i} a
    ((hgm a).mpr hav) (by rwa [hs]) (by
      intro n hn hout
      apply hmina n ((hgm n).mp hn)
      rwa [← hs])
  have hhi : h i = PowerSeries.X^5 := (hfix i (Set.mem_singleton i)).trans hgi
  let f := fun j : Fin e => h (i.succAbove j)
  refine ⟨f,?_,?_⟩
  · intro j
    exact horder _ (by simp)
  · have hrange : Set.range (parameterCoordinates 5 f) = Set.range h := by
      ext x
      constructor
      · rintro ⟨j,rfl⟩
        refine Fin.cases ?_ (fun j => ?_) j
        · exact ⟨i,hhi⟩
        · exact ⟨i.succAbove j,rfl⟩
      · rintro ⟨j,rfl⟩
        by_cases hj : j=i
        · subst j
          exact ⟨0,hhi.symm⟩
        · obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hj
          exact ⟨k.succ,by change h (i.succAbove k)=h j; rw [hk]⟩
    have heq : coordinateAlgebra (parameterCoordinates 5 f) = coordinateAlgebra h := by
      unfold coordinateAlgebra
      rw [hrange]
    exact (polynomialValues_eq_of_coordinateAlgebra_eq _ _ heq).trans
      ((polynomialValues_eq_of_coordinateAlgebra_eq _ _ he).trans hgS)

/-- No zero-coordinate germ realizes a positive numerical multiplicity. -/
theorem no_zero_dimensional_realization {S : NumericalSemigroup} (hm : HasMultiplicity S 5) :
    ¬AnalyticallyRealizes S 0 := by
  intro hreal
  obtain ⟨f,hf0,hfS⟩ := hreal.formal
  have hmem (n : ℕ) : n ∈ formalValues f ↔ n ∈ S.monoid := by rw [hfS]; rfl
  obtain ⟨i,_⟩ := exists_coordinate_of_minimal_value f hf0 5 (by omega)
    ((hmem 5).mpr hm.2.1) (by intro n hn; exact hm.2.2 n ((hmem n).mp hn))
  exact Fin.elim0 i

end HonestEmbeddingDimension
