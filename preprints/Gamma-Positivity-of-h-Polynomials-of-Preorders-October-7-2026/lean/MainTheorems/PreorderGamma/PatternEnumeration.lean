import MainTheorems.PreorderGamma.Patterns
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

omit [DecidableEq E] in
theorem mem_latticePoints {x : E → Fin (Fintype.card E + 1)} :
    x ∈ latticePoints ↔ IsLatticePoint (fun a => (x a).val) := by
  classical
  simp [latticePoints]

noncomputable def boxedLatticePointEquiv :
    (latticePoints (E := E)) ≃
      {x : E → Fin (Fintype.card E + 1) // IsLatticePoint fun a => (x a).val} := by
  exact
    { toFun := fun x => ⟨x.val, mem_latticePoints.mp x.property⟩
      invFun := fun x => ⟨x.val, mem_latticePoints.mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable def boxedPatternEquiv :
    (latticePoints (E := E)) ≃ SurplusPattern E :=
  boxedLatticePointEquiv.trans (latticePointEquiv.symm.trans latticePointPatternEquiv)

noncomputable instance : Fintype (SurplusPattern E) :=
  Fintype.ofEquiv (latticePoints (E := E)) boxedPatternEquiv

theorem supportPolynomial_eq_pattern_sum :
    supportPolynomial (E := E) =
      ∑ p : SurplusPattern E,
        (Polynomial.X : Polynomial ℕ) ^ (Fintype.card E - p.zeros.card) := by
  classical
  calc
    supportPolynomial (E := E) =
        ∑ x : latticePoints (E := E),
          (Polynomial.X : Polynomial ℕ) ^
            (Finset.univ.filter fun a => 0 < (x.val a).val).card :=
      (Finset.sum_coe_sort _ _).symm
    _ = ∑ p : SurplusPattern E,
        (Polynomial.X : Polynomial ℕ) ^ (Fintype.card E - p.zeros.card) := by
      apply Fintype.sum_equiv boxedPatternEquiv
      intro x
      let y : {x : E → ℕ // IsLatticePoint x} :=
        ⟨fun a => (x.val a).val, mem_latticePoints.mp x.property⟩
      have heq : patternPoint (pointPattern y) = y.val := patternPoint_pointPattern y
      change Polynomial.X ^ (Finset.univ.filter fun a => 0 < y.val a).card =
        Polynomial.X ^ (Fintype.card E - (pointPattern y).zeros.card)
      rw [← heq, patternPoint_support_card]

noncomputable def patternCount (z j : Finset E) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : SurplusPattern E => p.zeros = z ∧ p.high = j).card

theorem patternCount_eq_zero_of_not_disjoint {z j : Finset E} (hd : ¬Disjoint z j) :
    patternCount z j = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨_, hz, hj⟩ := Finset.mem_filter.mp hp
  have h := p.disjoint
  rw [hz, hj] at h
  exact hd h

theorem supportPolynomial_eq_pattern_counts :
    supportPolynomial (E := E) =
      ∑ q : Finset E × Finset E,
        Polynomial.C (patternCount q.1 q.2) *
          Polynomial.X ^ (Fintype.card E - q.1.card) := by
  classical
  rw [supportPolynomial_eq_pattern_sum]
  have h := Finset.sum_fiberwise'
    (Finset.univ : Finset (SurplusPattern E))
    (fun p => (p.zeros, p.high))
    (fun q : Finset E × Finset E =>
      (Polynomial.X : Polynomial ℕ) ^ (Fintype.card E - q.1.card))
  simpa [patternCount, Prod.ext_iff, Finset.sum_const, nsmul_eq_mul,
    Polynomial.C_eq_natCast] using h.symm

end ResearchMain.PreorderGamma
