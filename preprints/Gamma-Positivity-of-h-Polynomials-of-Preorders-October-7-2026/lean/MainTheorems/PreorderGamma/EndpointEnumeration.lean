import MainTheorems.PreorderGamma.EndpointDecomposition
import Mathlib.Data.Fintype.BigOperators

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

abbrev MatchedEndpoints (E : Type*) [Preorder E] :=
  {p : Finset E × Finset E // IsMatchedPair p.1 p.2}

noncomputable instance : Fintype (MatchedEndpoints E) := by
  classical
  unfold MatchedEndpoints
  infer_instance

abbrev CommonChoices (p : MatchedEndpoints E) :=
  ↥((Finset.univ \ (p.val.1 ∪ p.val.2)).powerset)

noncomputable instance (p : MatchedEndpoints E) : Fintype (CommonChoices p) := by
  classical
  unfold CommonChoices
  infer_instance

def separatedCommonEquiv : SeparatedEndpoints E ≃
    Σ p : MatchedEndpoints E, CommonChoices p where
  toFun p := ⟨⟨(p.left, p.right), p.matched⟩,
    ⟨p.common, Finset.mem_powerset.mpr
      (Finset.subset_sdiff.mpr ⟨Finset.subset_univ _, p.common_disjoint⟩)⟩⟩
  invFun p :=
    { left := p.1.val.1
      right := p.1.val.2
      common := p.2.val
      matched := p.1.property
      common_disjoint :=
        (Finset.subset_sdiff.mp (Finset.mem_powerset.mp p.2.property)).2 }
  left_inv p := by
    apply separatedEndpoints_ext <;> rfl
  right_inv p := by
    cases p
    rfl

noncomputable def endpointPolynomial : Polynomial ℕ :=
  ∑ p : OrderedEndpoints E, Polynomial.X ^ p.val.1.card

theorem endpointPolynomial_eq_common_sum :
    endpointPolynomial (E := E) =
      ∑ p : MatchedEndpoints E, ∑ c : CommonChoices p,
        (Polynomial.X : Polynomial ℕ) ^ (p.val.1.card + c.val.card) := by
  classical
  unfold endpointPolynomial
  rw [← Fintype.sum_sigma']
  apply Fintype.sum_equiv (endpointDecompositionEquiv.trans separatedCommonEquiv)
  intro p
  have h := separatedEndpoints_support_card (separateEndpoints p)
  have hp := endpointDecompositionEquiv.left_inv p
  change Polynomial.X ^ p.val.1.card =
    Polynomial.X ^ ((separateEndpoints p).left.card + (separateEndpoints p).common.card)
  rw [← h]
  exact congrArg (fun q : OrderedEndpoints E =>
    (Polynomial.X : Polynomial ℕ) ^ q.val.1.card) hp.symm

theorem matchedPair_common_sum {i j : Finset E} (hm : IsMatchedPair i j) :
    (∑ c ∈ (Finset.univ \ (i ∪ j)).powerset,
      (Polynomial.X : Polynomial ℕ) ^ (i.card + c.card)) =
      Polynomial.X ^ i.card * (1 + Polynomial.X) ^
        (Fintype.card E - 2 * i.card) := by
  classical
  have hc : (Finset.univ \ (i ∪ j)).card = Fintype.card E - 2 * i.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_union_of_disjoint hm.1, Finset.card_univ, matchedPair_card_eq hm]
    omega
  calc
    _ = Polynomial.X ^ i.card *
        ∑ c ∈ (Finset.univ \ (i ∪ j)).powerset,
          (Polynomial.X : Polynomial ℕ) ^ c.card := by
      simp only [pow_add, Finset.mul_sum]
    _ = Polynomial.X ^ i.card * (1 + Polynomial.X) ^
        (Finset.univ \ (i ∪ j)).card := by rw [powerset_support_sum]
    _ = _ := by rw [hc]

theorem commonChoices_sum (p : MatchedEndpoints E) :
    (∑ c : CommonChoices p,
      (Polynomial.X : Polynomial ℕ) ^ (p.val.1.card + c.val.card)) =
      Polynomial.X ^ p.val.1.card * (1 + Polynomial.X) ^
        (Fintype.card E - 2 * p.val.1.card) := by
  classical
  change (∑ c : (Finset.univ \ (p.val.1 ∪ p.val.2)).powerset,
    (Polynomial.X : Polynomial ℕ) ^ (p.val.1.card + c.val.card)) = _
  rw [Finset.sum_coe_sort ((Finset.univ \ (p.val.1 ∪ p.val.2)).powerset)
    (fun c : Finset E => (Polynomial.X : Polynomial ℕ) ^ (p.val.1.card + c.card))]
  exact matchedPair_common_sum p.property

noncomputable def allMatchedPairs : Finset (Finset E × Finset E) := by
  classical
  exact Finset.univ.filter fun p => IsMatchedPair p.1 p.2

omit [DecidableEq E] in
@[simp] theorem mem_allMatchedPairs {p : Finset E × Finset E} :
    p ∈ allMatchedPairs ↔ IsMatchedPair p.1 p.2 := by
  classical
  simp [allMatchedPairs]

noncomputable def matchedEndpointsFinsetEquiv : MatchedEndpoints E ≃
    ↥(allMatchedPairs (E := E)) where
  toFun p := ⟨p.val, mem_allMatchedPairs.mpr p.property⟩
  invFun p := ⟨p.val, mem_allMatchedPairs.mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq E] in
theorem allMatchedPairs_card_filter (k : ℕ) :
    (allMatchedPairs (E := E)).filter (fun p => p.1.card = k) = matchedPairs k := by
  classical
  ext p
  simp only [Finset.mem_filter, mem_allMatchedPairs, mem_matchedPairs]
  constructor
  · rintro ⟨hp, hk⟩
    exact ⟨hk, (matchedPair_card_eq hp).symm.trans hk, hp⟩
  · rintro ⟨hi, hj, hp⟩
    exact ⟨hp, hi⟩

omit [DecidableEq E] in
theorem matchingPolynomial_eq_endpoint_sum :
    matchingPolynomial (E := E) =
      ∑ p : MatchedEndpoints E,
        (Polynomial.X : Polynomial ℕ) ^ p.val.1.card *
          (1 + Polynomial.X) ^ (Fintype.card E - 2 * p.val.1.card) := by
  classical
  let w : ℕ → Polynomial ℕ := fun k =>
    Polynomial.X ^ k * (1 + Polynomial.X) ^ (Fintype.card E - 2 * k)
  have hbound : ∀ p ∈ allMatchedPairs (E := E),
      p.1.card ∈ Finset.range (Fintype.card E / 2 + 1) := by
    intro p hp
    have h := matchedPair_size_bound (mem_allMatchedPairs.mp hp)
    rw [Finset.mem_range]
    omega
  have hf := Finset.sum_fiberwise_of_maps_to' hbound w
  have hsum :
      (∑ p : MatchedEndpoints E, w p.val.1.card) =
        ∑ p ∈ allMatchedPairs (E := E), w p.1.card := by
    calc
      _ = ∑ p : allMatchedPairs (E := E), w p.val.1.card := by
        apply Fintype.sum_equiv matchedEndpointsFinsetEquiv
        intro p
        rfl
      _ = _ := Finset.sum_coe_sort (allMatchedPairs (E := E))
        (fun p : Finset E × Finset E => w p.1.card)
  change matchingPolynomial (E := E) = ∑ p : MatchedEndpoints E, w p.val.1.card
  rw [hsum]
  rw [← hf]
  simp only [allMatchedPairs_card_filter, Finset.sum_const, nsmul_eq_mul]
  simp only [matchingPolynomial, gammaCoefficient, w, mul_assoc]
  apply Finset.sum_congr rfl
  intro k hk
  exact congrArg
    (fun c : Polynomial ℕ => c * (Polynomial.X ^ k *
      (1 + Polynomial.X) ^ (Fintype.card E - 2 * k)))
    (Polynomial.C_eq_natCast (R := ℕ) (matchedPairs (E := E) k).card)

theorem endpointPolynomial_eq_matchingPolynomial :
    endpointPolynomial (E := E) = matchingPolynomial (E := E) := by
  rw [endpointPolynomial_eq_common_sum, matchingPolynomial_eq_endpoint_sum]
  apply Fintype.sum_congr
  intro p
  exact commonChoices_sum p

end ResearchMain.PreorderGamma
