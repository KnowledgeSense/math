import MainTheorems.PreorderGamma.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.EquivFin

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [Preorder E]

def IsMatchedPair (i j : Finset E) : Prop :=
  Disjoint i j ∧ ∃ f : i ≃ j, ∀ a : i, (a : E) ≤ (f a : E)

noncomputable def matchedPairs (k : ℕ) : Finset (Finset E × Finset E) := by
  classical
  exact Finset.univ.filter fun p =>
    p.1.card = k ∧ p.2.card = k ∧ IsMatchedPair p.1 p.2

noncomputable def gammaCoefficient (k : ℕ) : ℕ :=
  (matchedPairs (E := E) k).card

noncomputable def matchingPolynomial : Polynomial ℕ :=
  ∑ k ∈ Finset.range (Fintype.card E / 2 + 1),
    Polynomial.C (gammaCoefficient (E := E) k) *
      Polynomial.X ^ k * (1 + Polynomial.X) ^ (Fintype.card E - 2 * k)

@[simp] theorem mem_matchedPairs {k : ℕ} {p : Finset E × Finset E} :
    p ∈ matchedPairs k ↔ p.1.card = k ∧ p.2.card = k ∧ IsMatchedPair p.1 p.2 := by
  classical
  simp [matchedPairs]

omit [Fintype E] in
theorem matchedPair_card_eq {i j : Finset E} (h : IsMatchedPair i j) :
    i.card = j.card := by
  classical
  obtain ⟨hd, f, hf⟩ := h
  simpa using Fintype.card_congr f

theorem matchedPair_size_bound {i j : Finset E} (h : IsMatchedPair i j) :
    2 * i.card ≤ Fintype.card E := by
  classical
  have heq := matchedPair_card_eq h
  have hsum : i.card + j.card ≤ Fintype.card E := by
    rw [← Finset.card_union_of_disjoint h.1]
    exact Finset.card_le_univ _
  omega

omit [Fintype E] in
theorem empty_matchedPair : IsMatchedPair (∅ : Finset E) ∅ := by
  refine ⟨by simp, Equiv.refl (↥(∅ : Finset E)), ?_⟩
  intro a
  exact le_rfl

theorem matchedPairs_zero : matchedPairs (E := E) 0 = {(∅, ∅)} := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hi, hj, hm⟩ := mem_matchedPairs.mp hp
    apply Finset.mem_singleton.mpr
    exact Prod.ext (Finset.card_eq_zero.mp hi) (Finset.card_eq_zero.mp hj)
  · intro hp
    have hp' := Finset.mem_singleton.mp hp
    subst p
    exact mem_matchedPairs.mpr ⟨by simp, by simp, empty_matchedPair⟩

@[simp] theorem gammaCoefficient_zero : gammaCoefficient (E := E) 0 = 1 := by
  classical
  simp [gammaCoefficient, matchedPairs_zero]

theorem gammaCoefficient_eq_zero_of_large {k : ℕ} (hk : Fintype.card E < 2 * k) :
    gammaCoefficient (E := E) k = 0 := by
  classical
  have he : matchedPairs (E := E) k = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hi, hj, hm⟩ := mem_matchedPairs.mp hp
    have hb := matchedPair_size_bound hm
    omega
  simp [gammaCoefficient, he]

omit [Fintype E] [Preorder E] in
theorem powerset_support_sum (s : Finset E) :
    (∑ u ∈ s.powerset, (Polynomial.X : Polynomial ℕ) ^ u.card) =
      (1 + Polynomial.X) ^ s.card := by
  classical
  simpa using (Finset.prod_one_add (f := fun _ : E => (Polynomial.X : Polynomial ℕ)) s).symm

end ResearchMain.PreorderGamma
