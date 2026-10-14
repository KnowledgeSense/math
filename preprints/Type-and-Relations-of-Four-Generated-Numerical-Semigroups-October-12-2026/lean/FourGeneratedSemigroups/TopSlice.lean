import FourGeneratedSemigroups.StaircaseCorners
import FourGeneratedSemigroups.AperyMaximal

noncomputable section
namespace FourGeneratedSemigroups

/-- A staircase corner whose degree is not maximal in the semigroup Apéry set. -/
def spuriousCorners {S : NumericalSemigroup} (G : FourGenerated S) : Set Factorization :=
  {c | c∈staircaseCorners G ∧
    (factorizationMap G.generators c : ℤ)∉S.maximalApery (G.generators 0)}

/-- Below the top slice every staircase corner has genuinely maximal Apéry degree. -/
theorem corner_below_top_is_maximal {S : NumericalSemigroup} (G : FourGenerated S)
    (c : Factorization) (hc : c∈staircaseCorners G)
    (htop : c 3+1<criticalExponent G.generators G.positive 3) :
    (factorizationMap G.generators c : ℤ)∈S.maximalApery (G.generators 0) := by
  apply (maximalApery_iff_generator_tests G _).mpr
  refine ⟨hc.1.2.2,?_⟩
  intro i hi
  by_cases hi0 : i=0
  · subst i
    apply hi.2
    simpa using hc.1.2.2.1
  · apply hc.2 i hi0
    refine ⟨?_,?_,?_⟩
    · simp [Ne.symm hi0,hc.1.1]
    · by_cases hi3 : i=3
      · subst i; simpa using htop
      · simpa [Finsupp.single_apply,Ne.symm hi3] using hc.1.2.1
    · simpa using hi

/-- Spurious corners are confined to the top slice of the actual staircase. -/
theorem spuriousCorner_top {S : NumericalSemigroup} (G : FourGenerated S)
    (c : Factorization) (hc : c∈spuriousCorners G) :
    c 3+1=criticalExponent G.generators G.positive 3 := by
  have hlt := hc.1.1.2.1
  have hnot : ¬c 3+1<criticalExponent G.generators G.positive 3 :=
    fun h => hc.2 (corner_below_top_is_maximal G c hc.1 h)
  omega

end FourGeneratedSemigroups
