import MainTheorems.PreorderGamma.SupportRestriction
import MainTheorems.PreorderReciprocity.CommonBasisBijection

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]

def IsRelationMatchedPair (r : L → R → Prop) (I : Finset L) (B : Finset R) : Prop :=
  ∃ f : I ≃ B, ∀ a : I, r a.val (f a).val

abbrev RelationMatchedEndpoints (r : L → R → Prop) :=
  {p : Finset L × Finset R // IsRelationMatchedPair r p.1 p.2}

noncomputable instance (r : L → R → Prop) : Fintype (RelationMatchedEndpoints r) := by
  classical
  unfold RelationMatchedEndpoints
  infer_instance

omit [Fintype L] [Fintype R] in
theorem relationMatchedPair_card {r : L → R → Prop} {I : Finset L} {B : Finset R}
    (h : IsRelationMatchedPair r I B) : I.card = B.card := by
  obtain ⟨f, hf⟩ := h
  simpa only [Fintype.card_coe] using Fintype.card_congr f

omit [Fintype L] [Fintype R] in
theorem relationMatchedPair_swap {r : L → R → Prop} {I : Finset L} {B : Finset R}
    (h : IsRelationMatchedPair r I B) : IsRelationMatchedPair (fun b a => r a b) B I := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.symm, ?_⟩
  intro b
  simpa only [f.apply_symm_apply] using hf (f.symm b)

noncomputable def matchedSupportEndpointEquiv (r : L → R → Prop) :
    (Σ I : Finset L, MatchedSupport (fun b : R => fun a : I => r a.val b)) ≃
      RelationMatchedEndpoints r where
  toFun q := ⟨(q.1, q.2.val), by
    obtain ⟨f, hf⟩ := q.2.property.2
    refine ⟨f.symm, ?_⟩
    intro a
    simpa only [f.apply_symm_apply] using hf (f.symm a)⟩
  invFun p := ⟨p.val.1, ⟨p.val.2, by
    simpa only [Fintype.card_coe] using (relationMatchedPair_card p.property).symm, by
    obtain ⟨f, hf⟩ := p.property
    refine ⟨f.symm, ?_⟩
    intro b
    simpa only [f.apply_symm_apply] using hf (f.symm b)⟩⟩
  left_inv q := by
    cases q
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

noncomputable def relationMatchedEndpointSwap (r : L → R → Prop) :
    RelationMatchedEndpoints r ≃ RelationMatchedEndpoints (fun b a => r a b) where
  toFun p := ⟨p.val.swap, relationMatchedPair_swap p.property⟩
  invFun p := ⟨p.val.swap, relationMatchedPair_swap p.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

theorem supportEnumerator_eq_matched_endpoint_sum (r : L → R → Prop) :
    supportEnumerator r = ∑ p : RelationMatchedEndpoints r,
      (Polynomial.X : Polynomial ℕ) ^ p.val.1.card := by
  classical
  calc
    _ = ∑ I : Finset L,
        (Fintype.card (PositiveDemand (fun a : I => r a.val)) : Polynomial ℕ) *
          Polynomial.X ^ I.card := supportEnumerator_eq_positive_support_sum r
    _ = ∑ I : Finset L,
        (Fintype.card (MatchedSupport (fun b : R => fun a : I => r a.val b)) :
          Polynomial ℕ) * Polynomial.X ^ I.card := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [PreorderReciprocity.positive_demand_matched_support_count]
    _ = ∑ q : (Σ I : Finset L, MatchedSupport (fun b : R => fun a : I => r a.val b)),
        (Polynomial.X : Polynomial ℕ) ^ q.1.card := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := by
      apply Fintype.sum_equiv (matchedSupportEndpointEquiv r)
      intro q
      rfl

theorem supportEnumerator_transpose (r : L → R → Prop) :
    supportEnumerator r = supportEnumerator (fun b a => r a b) := by
  classical
  rw [supportEnumerator_eq_matched_endpoint_sum,
    supportEnumerator_eq_matched_endpoint_sum]
  apply Fintype.sum_equiv (relationMatchedEndpointSwap r)
  intro p
  change Polynomial.X ^ p.val.1.card = Polynomial.X ^ p.val.2.card
  rw [relationMatchedPair_card p.property]

theorem supportEnumerator_coeff_transpose (r : L → R → Prop) (k : ℕ) :
    (supportEnumerator r).coeff k = (supportEnumerator (fun b a => r a b)).coeff k := by
  rw [supportEnumerator_transpose r]

end ResearchMain.PreorderGamma
