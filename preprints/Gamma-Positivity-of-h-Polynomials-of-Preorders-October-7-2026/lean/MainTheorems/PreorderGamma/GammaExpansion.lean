import MainTheorems.PreorderGamma.SupportDuality
import MainTheorems.PreorderGamma.EndpointEnumeration

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

noncomputable def preorderRelationEndpointEquiv :
    RelationMatchedEndpoints (fun a b : E => b ≤ a) ≃ OrderedEndpoints E where
  toFun p := ⟨p.val.swap, by
    obtain ⟨f, hf⟩ := p.property
    refine ⟨f.symm, ?_⟩
    intro b
    simpa only [f.apply_symm_apply] using hf (f.symm b)⟩
  invFun p := ⟨p.val.swap, by
    obtain ⟨f, hf⟩ := p.property
    refine ⟨f.symm, ?_⟩
    intro b
    simpa only [f.apply_symm_apply] using hf (f.symm b)⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

theorem supportPolynomial_eq_endpointPolynomial :
    supportPolynomial (E := E) = endpointPolynomial (E := E) := by
  classical
  rw [supportPolynomial_eq_preorderEnumerator, supportEnumerator_eq_matched_endpoint_sum]
  unfold endpointPolynomial
  apply Fintype.sum_equiv preorderRelationEndpointEquiv
  intro p
  change Polynomial.X ^ p.val.1.card = Polynomial.X ^ p.val.2.card
  rw [relationMatchedPair_card p.property]

theorem supportPolynomial_eq_matchingPolynomial :
    supportPolynomial (E := E) = matchingPolynomial (E := E) := by
  rw [supportPolynomial_eq_endpointPolynomial, endpointPolynomial_eq_matchingPolynomial]

theorem preorder_gamma_expansion : supportPolynomial (E := E) =
    ∑ k ∈ Finset.range (Fintype.card E / 2 + 1),
      Polynomial.C (gammaCoefficient (E := E) k) *
        Polynomial.X ^ k * (1 + Polynomial.X) ^ (Fintype.card E - 2 * k) :=
  supportPolynomial_eq_matchingPolynomial

end ResearchMain.PreorderGamma
