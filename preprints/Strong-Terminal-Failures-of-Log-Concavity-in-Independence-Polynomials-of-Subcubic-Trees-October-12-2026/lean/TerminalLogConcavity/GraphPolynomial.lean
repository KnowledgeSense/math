import TerminalLogConcavity.GraphConstruction
import TerminalLogConcavity.GraphInvariants
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Reverse

namespace TerminalLogConcavity
open Finset Polynomial
open scoped Polynomial
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- The independence polynomial, defined by enumerating actual independent vertex sets. -/
noncomputable def independencePolynomial (s : Finset V) : ℕ[X] :=
  ∑ t ∈ independentSetsWithin G s, X ^ t.card

omit [DecidableEq V] in
@[simp] theorem independencePolynomial_empty : independencePolynomial G ∅ = 1 := by
  simp [independencePolynomial]

theorem independencePolynomial_recursion (s : Finset V) (r : V) (hr : r ∈ s) :
    independencePolynomial G s = independencePolynomial G (s.erase r) +
      X * independencePolynomial G (compatibleVertices G s r) := by
  classical
  unfold independencePolynomial
  rw [independentSetsWithin_decomposition G s r hr,
    sum_union (independent_decomposition_disjoint G s r),
    sum_image (insert_injective_on_compatible G s r)]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro t ht
  have hrt : r ∉ t := fun h => compatible_not_mem G s r (((mem_independentSetsWithin G).mp ht).1 h)
  rw [card_insert_of_notMem hrt, pow_succ, mul_comm]

theorem independencePolynomial_union {a b : Finset V} (hd : Disjoint a b)
    (he : Separated G a b) :
    independencePolynomial G (a ∪ b) = independencePolynomial G a * independencePolynomial G b := by
  classical
  unfold independencePolynomial
  rw [independentSetsWithin_union G he,
    sum_image (union_injective_on_independentSets G hd), sum_mul_sum, sum_product]
  apply sum_congr rfl
  intro a hpa
  apply sum_congr rfl
  intro b hpb
  rw [card_union_of_disjoint (hd.mono ((mem_independentSetsWithin G).mp hpa).1
    ((mem_independentSetsWithin G).mp hpb).1), pow_add]

omit [DecidableEq V] in
theorem independencePolynomial_natDegree_le (s : Finset V) :
    (independencePolynomial G s).natDegree ≤ independenceNumber G s := by
  apply natDegree_sum_le_of_forall_le
  intro t ht
  rw [natDegree_X_pow]
  obtain ⟨hsub, hi⟩ := (mem_independentSetsWithin G).mp ht
  exact independent_card_le G s hsub hi

omit [DecidableEq V] in
theorem independencePolynomial_coeff (s : Finset V) (k : ℕ) :
    (independencePolynomial G s).coeff k =
      ((independentSetsWithin G s).filter (fun t => t.card = k)).card := by
  classical
  simp [independencePolynomial, coeff_X_pow, eq_comm]

/-- Ordinary conditional polynomial pair for a recursively constructed rooted forest. -/
noncomputable def ForestExpr.polynomials : ForestExpr → ℕ[X] × ℕ[X]
  | .empty => (1, 1)
  | .union A B => (A.polynomials.1 * B.polynomials.1, A.polynomials.2 * B.polynomials.2)
  | .root A => (A.polynomials.1 + X * A.polynomials.2, A.polynomials.1)

def ForestExpr.alpha : ForestExpr → ℕ
  | .empty => 0
  | .union A B => A.alpha + B.alpha
  | .root A => A.alpha + (if flag A then 0 else 1)

theorem ForestRealization.alpha_eq {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) : independenceNumber G s = A.alpha := by
  induction h with
  | empty => simp [ForestExpr.alpha]
  | union hd he hA hB ihA ihB => rw [independenceNumber_union G hd he, ihA, ihB]; rfl
  | root r hr he hA ih => rw [hA.root_independenceNumber G hr he, ih]; rfl

theorem ForestRealization.polynomials_eq {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) :
    independencePolynomial G s = A.polynomials.1 ∧
      independencePolynomial G (s \ rs) = A.polynomials.2 := by
  induction h with
  | empty => simp [ForestExpr.polynomials]
  | @union a b ra rb A B hd he hA hB ihA ihB =>
    have hd' : Disjoint (a \ ra) (b \ rb) := hd.mono sdiff_subset sdiff_subset
    have he' := he.mono G (sdiff_subset (s := a) (t := ra)) (sdiff_subset (s := b) (t := rb))
    rw [independencePolynomial_union G hd he,
      roots_deleted_union hd (hA.roots_subset G) (hB.roots_subset G),
      independencePolynomial_union G hd' he', ihA.1, ihA.2, ihB.1, ihB.2]
    exact ⟨rfl, rfl⟩
  | @root s rs A r hr he hA ih =>
    have hc := independencePolynomial_recursion G (insert r s) r (mem_insert_self _ _)
    rw [erase_insert hr, compatibleVertices_root G hr he, ih.1, ih.2] at hc
    constructor
    · exact hc
    · rw [sdiff_singleton_eq_erase, erase_insert hr, ih.1]
      rfl

theorem ForestExpr.graph_polynomial (A : ForestExpr) :
    independencePolynomial A.graph univ = A.polynomials.1 := by
  obtain ⟨rs, h, _⟩ := A.realization
  exact (h.polynomials_eq A.graph).1

theorem ForestExpr.graph_alpha (A : ForestExpr) : A.graph.indepNum = A.alpha := by
  obtain ⟨rs, h, _⟩ := A.realization
  rw [← independenceNumber_univ A.graph]
  exact h.alpha_eq A.graph

theorem ForestExpr.root_deleted_polynomial (A : ForestExpr) :
    independencePolynomial (ForestExpr.root A).graph (univ.erase none) = A.polynomials.1 := by
  obtain ⟨rs, h, hr⟩ := (ForestExpr.root A).realization
  have he : rs = {none} := by
    ext v
    cases v <;> simp [hr, ForestExpr.IsRoot]
  simpa [he, sdiff_singleton_eq_erase, ForestExpr.polynomials] using (h.polynomials_eq _).2

end TerminalLogConcavity
