import EmbeddingDimensionStrata.DenseGeneration

/-! # Canonical normal-form generators and their generation theorems -/
noncomputable section
namespace EmbeddingDimensionStrata
open scoped PowerSeries.WithPiTopology
variable {K : Type*} [Field K] [TopologicalSpace K]

/-- The five values, in the order used in the paper. -/
def generatorValue (i : Fin 5) : ℕ :=
  match i.val with
  | 0 => 10
  | 1 => 11
  | 2 => 34
  | 3 => 46
  | _ => 58

theorem generatorValue_lt (i : Fin 5) : generatorValue i < 60 := by
  have h : ∀ j : Fin 5, generatorValue j < 60 := by decide
  exact h i

theorem generatorValue_gamma (i : Fin 5) : Gamma (generatorValue i) := by
  rw [gamma_below_conductor (generatorValue_lt i)]
  have h : ∀ j : Fin 5, generatorValue j ∈ valuesBelowConductor := by decide
  exact h i

/-- The unique actual normal-form generator of each of the five orders. -/
def normalGenerator (S : CompleteGammaSubalgebra (K := K)) (i : Fin 5) : PowerSeries K :=
  Classical.choose (existsUnique_normalForm S (generatorValue_lt i) (generatorValue_gamma i))

theorem normalGenerator_mem (S : CompleteGammaSubalgebra (K := K)) (i : Fin 5) :
    normalGenerator S i ∈ S.val :=
  (Classical.choose_spec
    (existsUnique_normalForm S (generatorValue_lt i) (generatorValue_gamma i))).1.1

theorem normalGenerator_normal (S : CompleteGammaSubalgebra (K := K)) (i : Fin 5) :
    IsNormalForm (generatorValue i) (normalGenerator S i) :=
  (Classical.choose_spec
    (existsUnique_normalForm S (generatorValue_lt i) (generatorValue_gamma i))).1.2

/-- Polynomial expressions in the five canonical generators. -/
def normalGeneratorAlgebra (S : CompleteGammaSubalgebra (K := K)) :
    Subalgebra K (PowerSeries K) := Algebra.adjoin K (Set.range (normalGenerator S))

theorem normalGeneratorAlgebra_le (S : CompleteGammaSubalgebra (K := K)) :
    normalGeneratorAlgebra S ≤ S.val := by
  apply Algebra.adjoin_le
  rintro f ⟨i, rfl⟩
  exact normalGenerator_mem S i

theorem normalGeneratorAlgebra_values (S : CompleteGammaSubalgebra (K := K))
    (n : ℕ) (hn : HasValue S.val n) : HasValue (normalGeneratorAlgebra S) n := by
  have hv : ∀ i : Fin 5, HasValue (normalGeneratorAlgebra S) (generatorValue i) := by
    intro i
    exact ⟨normalGenerator S i,
      Algebra.subset_adjoin (Set.mem_range_self i), (normalGenerator_normal S i).hasOrder⟩
  exact hasValue_of_gamma (normalGeneratorAlgebra S)
    (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) ((S.property.2 n).mp hn)

/-- The five canonical generators generate the complete algebra in the formal topology. -/
theorem normalGeneratorAlgebra_closure [DiscreteTopology K]
    (S : CompleteGammaSubalgebra (K := K)) :
    (normalGeneratorAlgebra S).topologicalClosure = S.val := by
  apply le_antisymm
  · exact Subalgebra.topologicalClosure_minimal (normalGeneratorAlgebra_le S) S.property.1
  · exact le_closure_of_same_values (normalGeneratorAlgebra S) S.val
      (normalGeneratorAlgebra_le S) (normalGeneratorAlgebra_values S)

/-- Their conductor-60 images generate the truncated algebra as an algebra. -/
theorem normalGeneratorAlgebra_jet (S : CompleteGammaSubalgebra (K := K)) :
    (normalGeneratorAlgebra S).map (jetMap K 60) = S.val.map (jetMap K 60) :=
  map_jet_eq_of_same_values (normalGeneratorAlgebra S) S.val
    (normalGeneratorAlgebra_le S) (normalGeneratorAlgebra_values S) 60

/-- Equality of the five actual normal forms forces equality of complete
embedded subalgebras. -/
theorem normalGenerator_injective [DiscreteTopology K] :
    Function.Injective (normalGenerator (K := K)) := by
  intro S T h
  apply Subtype.ext
  rw [← normalGeneratorAlgebra_closure S, ← normalGeneratorAlgebra_closure T]
  congr 1
  exact congrArg (fun f : Fin 5 → PowerSeries K => Algebra.adjoin K (Set.range f)) h

end EmbeddingDimensionStrata
