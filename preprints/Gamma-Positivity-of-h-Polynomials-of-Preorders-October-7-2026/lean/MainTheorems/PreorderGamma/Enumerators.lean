import MainTheorems.PreorderGamma.LatticePoints
import Mathlib.Algebra.Polynomial.Coeff

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]

noncomputable def demandVectors (r : L → R → Prop) :
    Finset (L → Fin (Fintype.card R + 1)) := by
  classical
  exact Finset.univ.filter fun d => IsDemand r fun a => (d a).val

noncomputable def supportEnumerator (r : L → R → Prop) : Polynomial ℕ :=
  ∑ d ∈ demandVectors r,
    Polynomial.X ^ (demandSupport fun a => (d a).val).card

theorem supportEnumerator_coeff (r : L → R → Prop) (k : ℕ) :
    (supportEnumerator r).coeff k =
      ((demandVectors r).filter fun d =>
        (demandSupport fun a => (d a).val).card = k).card := by
  classical
  simp only [supportEnumerator, Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_pow, Finset.card_filter, eq_comm]

theorem supportEnumerator_coeff_zero_of_large (r : L → R → Prop) {k : ℕ}
    (hk : Fintype.card R < k) : (supportEnumerator r).coeff k = 0 := by
  classical
  rw [supportEnumerator_coeff]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨hd, hcard⟩ := Finset.mem_filter.mp hd
  have hdemand : IsDemand r (fun a => (d a).val) :=
    (Finset.mem_filter.mp hd).2
  have hbound := support_card_le_right hdemand
  omega

theorem supportEnumerator_fullSupport_coeff (r : L → R → Prop) :
    (supportEnumerator r).coeff (Fintype.card L) =
      ((demandVectors r).filter fun d => ∀ a, 0 < (d a).val).card := by
  classical
  rw [supportEnumerator_coeff]
  congr 1
  ext d
  simp only [Finset.mem_filter, demandSupport]
  have h : (Finset.univ.filter fun a => 0 < (d a).val).card = Fintype.card L ↔
      ∀ a, 0 < (d a).val := by
    simpa using (Finset.card_filter_eq_iff
      (s := (Finset.univ : Finset L)) (p := fun a => 0 < (d a).val))
  exact and_congr_right fun _ => h

variable {E : Type*} [Fintype E] [Preorder E]

theorem latticePoints_eq_preorderDemands :
    latticePoints (E := E) = demandVectors (fun a b : E => b ≤ a) := by
  classical
  ext x
  simp [latticePoints, demandVectors, isLatticePoint_iff_preorderDemand]

theorem supportPolynomial_eq_preorderEnumerator :
    supportPolynomial (E := E) = supportEnumerator (fun a b : E => b ≤ a) := by
  classical
  simp only [supportPolynomial, supportEnumerator,
    latticePoints_eq_preorderDemands, demandSupport]

end ResearchMain.PreorderGamma
