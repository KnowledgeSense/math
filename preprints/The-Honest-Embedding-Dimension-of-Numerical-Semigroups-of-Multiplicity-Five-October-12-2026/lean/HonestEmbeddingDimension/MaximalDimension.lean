import HonestEmbeddingDimension.NonparameterNormalForm
import HonestEmbeddingDimension.MonomialValues
import HonestEmbeddingDimension.MontgomeryRealization

namespace HonestEmbeddingDimension

theorem analytic_realization_embeddingDimension {S : NumericalSemigroup} {m : ℕ}
    (hm : HasMultiplicity S m) : AnalyticallyRealizes S S.embeddingDimension := by
  let G := NumericalSemigroup.orderedMinimalGenerators hm
  exact monomial_analytic_realization G.generators (fun i => (G.isMinimal i).1) G.generates

/-- The maximal-dimension obstruction is proved for every analytic ambient dimension. -/
theorem five_generator_maximal_dimension_lower {S : NumericalSemigroup} {a b c d e : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) (hd : d<2*a)
    (hreal : AnalyticallyRealizes S e) : 5 ≤ e := by
  cases e with
  | zero => exact False.elim (no_zero_dimensional_realization hm hreal)
  | succ e =>
    obtain ⟨ha,hmina,_,_,_,_⟩ := h.normalization_data hm
    have h5a := h.five_lt_a
    have hab := h.a_lt_b
    have hbc := h.b_lt_c
    have hcd := h.c_lt_d
    obtain ⟨f,hf,hfS⟩ := parameterized_normal_form hm (by omega) h.minimal.2.1.2.1 ha hmina hreal.formal
    apply linear_low_residue_bound (m := 5) (a := a) (N := 2*a) (by omega) f hf le_rfl
      (![0,a,b,c,d] : Fin 5 → ℕ)
      (by intro i; fin_cases i <;> dsimp <;> omega) (five_generator_basis_residues_injective hm h)
    intro i
    rw [hfS]
    fin_cases i
    · exact S.monoid.zero_mem
    · exact h.minimal.2.1.2.1
    · exact h.minimal.2.2.1.2.1
    · exact h.minimal.2.2.2.1.2.1
    · exact h.minimal.2.2.2.2.2.1

/-- The maximal honest embedding dimension clause, including both original directions. -/
theorem honest_dimension_five_iff {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) :
    HasHonestEmbeddingDimension S 5 ↔ d<2*a := by
  constructor
  · intro hdim
    by_contra hnot
    have hdgt : 2*a<d := by have := five_generator_last_ne_twice_first h; omega
    have hfour := analytic_realization_five_nonmaximal hm h hdgt
    have hh := hdim.2 4 hfour
    omega
  · intro hd
    have hmono := analytic_realization_embeddingDimension hm
    rw [h.embeddingDimension_eq] at hmono
    exact ⟨hmono,fun _ he => five_generator_maximal_dimension_lower hm h hd he⟩

end HonestEmbeddingDimension
