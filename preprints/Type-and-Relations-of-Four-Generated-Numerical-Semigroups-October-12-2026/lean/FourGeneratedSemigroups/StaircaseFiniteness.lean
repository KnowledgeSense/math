import FourGeneratedSemigroups.ArtinianReduction
import FourGeneratedSemigroups.FactorizationClasses
import FourGeneratedSemigroups.StaircaseBoundary

noncomputable section
namespace FourGeneratedSemigroups

/-- Finiteness follows from actual finite Apéry degrees and actual finite factorization fibers. -/
theorem finite_staircase {S : NumericalSemigroup} (G : FourGenerated S) :
    (staircase G).Finite := by
  let := finite_aperyDegree G
  have hf : ∀ n : AperyDegree G,
      {a : Factorization | factorizationMap G.generators a=n.val}.Finite := by
    intro n
    exact Set.finite_coe_iff.mp (finite_factorizations G.generators G.positive n.val)
  have hh := Set.finite_iUnion hf
  apply hh.subset
  intro a ha
  exact Set.mem_iUnion.mpr ⟨⟨factorizationMap G.generators a,ha.2.2⟩,rfl⟩

noncomputable def staircaseGeneratorNumber {S : NumericalSemigroup} (G : FourGenerated S) : ℕ :=
  Nat.card {a : Factorization // a∈staircaseBoundary G ∧ a 0=0}

noncomputable def fullSupportGeneratorNumber {S : NumericalSemigroup} (G : FourGenerated S) : ℕ :=
  Nat.card {a : Factorization // a∈staircaseBoundary G ∧ a 0=0 ∧ 0<a 1 ∧ 0<a 2 ∧ 0<a 3}

end FourGeneratedSemigroups
