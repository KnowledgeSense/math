import HilbertBipartite.Ideals
import HilbertBipartite.StandardMonomials

noncomputable section
namespace HilbertBipartite
open MvPolynomial

theorem squarePower_mem_generatorPowerExponents (p q s : ℕ) (i : Fin p ⊕ Fin q) :
    Finsupp.single i (2*s) ∈ generatorPowerExponents (bipartiteGeneratorExponents p q) s := by
  induction s with
  | zero => simp [generatorPowerExponents]
  | succ s ih =>
    refine ⟨Finsupp.single i 2, Or.inl ⟨i,rfl⟩, Finsupp.single i (2*s), ih, ?_⟩
    rw [← Finsupp.single_add]
    congr 1
    omega

theorem standardPowerExponent_bound {p q s : ℕ}
    {a : (Fin p ⊕ Fin q) →₀ ℕ}
    (ha : a ∉ bipartitePowerExponents p q s) (i : Fin p ⊕ Fin q) : a i < 2*s := by
  by_contra h
  apply ha
  exact ⟨Finsupp.single i (2*s), squarePower_mem_generatorPowerExponents p q s i,
    Finsupp.single_le_iff.mpr (Nat.le_of_not_gt h)⟩

/-- Every actual quotient has finitely many standard exponents, because the
ideal contains the `2s`-th power of every variable. -/
theorem finite_standardPowerExponents (p q s : ℕ) :
    ((bipartitePowerExponents p q s)ᶜ).Finite := by
  classical
  let box := (Finset.univ : Finset (Fin p ⊕ Fin q)).finsupp
    (fun _ => Finset.range (2*s))
  apply box.finite_toSet.subset
  intro a ha
  simpa [box, Finset.mem_finsupp_iff] using
    (standardPowerExponent_bound ha)

/-- Reindex standard exponents by the finite enumeration used for counting. -/
noncomputable def standardPowerExponentEquiv (p q s : ℕ)
    (h : ∀ a b, Finsupp.sumElim a b ∈ bipartitePowerExponents p q s ↔
      PowerCriterion s a b) :
    ↥((bipartitePowerExponents p q s)ᶜ) ≃ ↥(standardExponents p q s) := by
  let e : ((Fin p ⊕ Fin q) →₀ ℕ) ≃ ExponentPair p q :=
    Finsupp.sumFinsuppEquivProdFinsupp
  refine e.subtypeEquiv ?_
  intro a
  change a ∉ bipartitePowerExponents p q s ↔ e a ∈ standardExponents p q s
  rw [mem_standardExponents]
  have hh := h (e a).1 (e a).2
  have he : Finsupp.sumElim (e a).1 (e a).2 = a := e.symm_apply_apply a
  rw [he] at hh
  exact not_congr hh

/-- Identifying generator decomposition by its numerical criterion proves the
quotient dimension equals the number of enumerated standard exponents. -/
theorem finrank_bipartite_quotient_eq_standard_card
    (K : Type*) [Field K] (p q s : ℕ)
    (h : ∀ a b, Finsupp.sumElim a b ∈ bipartitePowerExponents p q s ↔
      PowerCriterion s a b) :
    Module.finrank K (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s) =
      (standardExponents p q s).card := by
  let e := standardPowerExponentEquiv p q s h
  let : Fintype ↥((bipartitePowerExponents p q s)ᶜ) := Fintype.ofEquiv _ e.symm
  rw [finrank_monomial_quotient _ _ (mem_bipartiteIdeal_pow_iff_support p q s)]
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

end HilbertBipartite
