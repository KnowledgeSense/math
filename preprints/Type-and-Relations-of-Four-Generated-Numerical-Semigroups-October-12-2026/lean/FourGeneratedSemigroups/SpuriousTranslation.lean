import FourGeneratedSemigroups.CornerOrder
import FourGeneratedSemigroups.FullSupportBoundary

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma spurious_add_third_apery (a : Factorization) (ha : a∈spuriousCorners G) :
    (factorizationMap G.generators a : ℤ)+(G.generators 3 : ℤ)∈S.apery (G.generators 0) := by
  by_contra h3
  apply ha.2
  apply (maximalApery_iff_generator_tests G _).mpr
  refine ⟨ha.1.1.2.2,?_⟩
  intro i hi
  fin_cases i
  · apply hi.2
    simpa using ha.1.1.2.2.1
  · apply ha.1.2 1 (by decide)
    refine ⟨by simp [ha.1.1.1],by simpa using ha.1.1.2.1,by simpa using hi⟩
  · apply ha.1.2 2 (by decide)
    refine ⟨by simp [ha.1.1.1],by simpa using ha.1.1.2.1,by simpa using hi⟩
  · exact h3 hi

/-- A spurious top corner becomes standard after the critical binomial shifts
its first two coordinates and removes its third coordinate. -/
theorem spurious_translation_mem (p : Factorization) (hp0 : p 0=0) (hp3 : p 3=0)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3)
    (a : Factorization) (ha : a∈spuriousCorners G) :
    a.erase 3+p∈staircase G := by
  have ht := spuriousCorner_top G a ha
  have hs := factorizationMap_split G.generators a 3
  have hw : factorizationMap G.generators (a.erase 3+p)=
      factorizationMap G.generators a+G.generators 3 := by
    rw [map_add,hp]
    nlinarith
  refine ⟨?_,?_,?_⟩
  · simp [hp0,ha.1.1.1]
  · simpa [hp3] using (criticalExponent_spec G.generators G.positive 3).1
  · simpa [hw] using spurious_add_third_apery G a ha

end FourGeneratedSemigroups
