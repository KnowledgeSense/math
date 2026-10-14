import FourGeneratedSemigroups.ReductionSocle
import FourGeneratedSemigroups.StaircaseSocle

noncomputable section
namespace FourGeneratedSemigroups
variable (K : Type*) [Field K] {S : NumericalSemigroup} (G : FourGenerated S)

/-- When all three critical relations reach generator zero, every Apéry
factorization already belongs to the bounded staircase. -/
lemma apery_factorization_mem_staircase
    (h30 : CriticalArc G.generators G.positive 3 0) (a : Factorization)
    (ha : (factorizationMap G.generators a : ℤ)∈S.apery (G.generators 0)) :
    a∈staircase G :=
  ⟨G.factorization_coordinate_zero_of_apery 0 a ha,
    apery_coordinate_lt_of_criticalArc G 3 h30 a ha,ha⟩

/-- The actual Artinian reduction is monomial in the all-arcs-to-zero case. -/
theorem reductionIdeal_eq_staircaseIdeal
    (hG : PrimaryOrdering G) (h30 : CriticalArc G.generators G.positive 3 0) :
    reductionIdeal K G=staircaseIdeal K G := by
  apply le_antisymm
  · apply sup_le
    · rw [definingIdeal_eq_binomial_span,Ideal.span_le]
      rintro f ⟨a,b,hab,rfl⟩
      by_cases ha : (factorizationMap G.generators a : ℤ)∈S.apery (G.generators 0)
      · have hb : (factorizationMap G.generators b : ℤ)∈S.apery (G.generators 0) := hab ▸ ha
        have he := primary_staircase_weight_injective G hG
          (apery_factorization_mem_staircase G h30 a ha)
          (apery_factorization_mem_staircase G h30 b hb) (congrArg (fun n : ℕ => (n : ℤ)) hab)
        simp [he]
      · apply Ideal.sub_mem
        · apply (monomial_mem_staircaseIdeal_iff K G a).mpr
          exact fun h => ha h.2.2
        · apply (monomial_mem_staircaseIdeal_iff K G b).mpr
          intro hb
          exact ha (hab.symm ▸ hb.2.2)
    · rw [Ideal.span_le,Set.singleton_subset_iff]
      exact zero_variable_mem_staircaseIdeal K G
  · rw [staircaseIdeal,Ideal.span_le]
    rintro f ⟨a,ha,rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply reduction_monomial_zero_of_not_apery K G
    exact fun hh => ha (apery_factorization_mem_staircase G h30 a hh)

/-- In the monomial case the staircase corner count is the original semigroup type. -/
theorem type_eq_staircaseCorners_of_all_arcs
    (hG : PrimaryOrdering G) (h30 : CriticalArc G.generators G.positive 3 0) :
    S.type=Nat.card (staircaseCorners G) := by
  let socleDimension (I : Ideal (MvPolynomial (Fin 4) ℚ)) : ℕ :=
    Module.finrank ℚ (show Submodule ℚ (MvPolynomial (Fin 4) ℚ ⧸ I) from
      { carrier := {q | ∀ i : Fin 4,q*Ideal.Quotient.mk I (MvPolynomial.X i)=0}
        zero_mem' := by simp
        add_mem' := by intro a b ha hb i; simp [add_mul,ha i,hb i]
        smul_mem' := by intro a b hb i; simp [smul_mul_assoc,hb i] })
  have ht : S.type=socleDimension (reductionIdeal ℚ G) :=
    type_eq_finrank_reductionSocle ℚ G
  rw [reductionIdeal_eq_staircaseIdeal ℚ G hG h30] at ht
  change S.type=Module.finrank ℚ (staircaseSocle ℚ G) at ht
  exact ht.trans (finrank_staircaseSocle ℚ G (finite_primary_staircase G hG))

end FourGeneratedSemigroups
