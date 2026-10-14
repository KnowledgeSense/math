import EmbeddingDimensionStrata.Reduction

/-! # The 27-dimensional basis of genuine Γ-subalgebras -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

/-- Distinct monic orders below the cutoff give linear independence in the
actual quotient. -/
theorem linearIndependent_jet_of_monic {ι : Type*} [Fintype ι]
    (v : ι → Fin 60) (hv : Function.Injective v)
    (f : ι → PowerSeries K) (hf : ∀ i, MonicAt (f i) (v i).val) :
    LinearIndependent K (fun i => jetMap K 60 (f i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hind : ∀ n : ℕ, ∀ j : ι, (v j).val = n → a j = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      have heq := congrArg (fun x => jetCoeff 60 (v j) x) ha
      simp only [map_sum, map_smul, jetCoeff_jetMap, map_zero, smul_eq_mul] at heq
      rw [Finset.sum_eq_single j] at heq
      · simpa only [(hf j).2, mul_one] using heq
      · intro k _ hkj
        by_cases hlt : (v k).val < (v j).val
        · rw [ih (v k).val (by omega) k rfl, zero_mul]
        · have hne : (v k).val ≠ (v j).val := by
            intro hh
            exact hkj (hv (Fin.ext hh))
          rw [(hf k).1 (v j).val (by omega), mul_zero]
      · intro hh
        exact False.elim (hh (Finset.mem_univ j))
  exact hind (v i).val i rfl

/-- The semigroup values below the conductor, retaining their natural-number
meaning rather than arbitrary coordinate labels. -/
abbrev ValueIndex := {n : ℕ // n ∈ valuesBelowConductor}

theorem valueIndex_lt (i : ValueIndex) : i.val < 60 := by
  have h : ∀ n ∈ valuesBelowConductor, n < 60 := by decide
  exact h i.val i.property

theorem valueIndex_card : Fintype.card ValueIndex = 27 := by decide

theorem basisJets_linearIndependent (p : NormalCoordinate → K) :
    LinearIndependent K (fun k : ValueIndex => jetMap K 60 (basisSeries p k.val)) := by
  apply linearIndependent_jet_of_monic
    (v := fun i : ValueIndex => ⟨i.val,valueIndex_lt i⟩)
  · intro i j h
    exact Subtype.ext (congrArg Fin.val h)
  · intro i
    exact basisSeries_monic p i.val i.property

theorem basisJetSpace_finrank (p : NormalCoordinate → K) :
    Module.finrank K (basisJetSpace p) = 27 := by
  rw [basisJetSpace, finrank_span_eq_card (basisJets_linearIndependent p)]
  exact valueIndex_card

/-- Every genuine finite Γ-algebra has dimension 27 over its coefficient field. -/
theorem parameterJetAlgebra_finrank (p : ParameterSpace (K := K)) :
    Module.finrank K (parameterJetAlgebra p.val) = 27 := by
  rw [← (parameterJetAlgebra p.val).finrank_toSubmodule,
    parameterSpace_eq_basisJetSpace]
  exact basisJetSpace_finrank p.val

end EmbeddingDimensionStrata
