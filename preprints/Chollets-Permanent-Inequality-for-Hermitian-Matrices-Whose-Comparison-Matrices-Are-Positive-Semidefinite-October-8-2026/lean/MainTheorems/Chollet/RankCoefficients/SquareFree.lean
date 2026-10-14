import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

open MvPolynomial

variable {I : Type*} [DecidableEq I]

def squareIdeal (I : Type*) : Ideal (MvPolynomial I ℂ) :=
  Ideal.span (Set.range fun i : I => (X i : MvPolynomial I ℂ) ^ 2)

abbrev SquareFree (I : Type*) := MvPolynomial I ℂ ⧸ squareIdeal I

def scalar (c : ℂ) : SquareFree I := Ideal.Quotient.mk (squareIdeal I) (C c)

def scalarHom : ℂ →+* SquareFree I := (Ideal.Quotient.mk (squareIdeal I)).comp C

def rowVariable (i : I) : SquareFree I := Ideal.Quotient.mk (squareIdeal I) (X i)

def monomial (s : Finset I) : SquareFree I := ∏ i ∈ s, rowVariable i

def rooted (s : Finset I) (c : I → ℂ) : SquareFree I :=
  ∑ i ∈ s, scalar (c i) * monomial (s.erase i)

omit [DecidableEq I] in
@[simp] theorem scalar_zero : scalar (0 : ℂ) = (0 : SquareFree I) := by
  simp [scalar]

omit [DecidableEq I] in
@[simp] theorem scalar_one : scalar (1 : ℂ) = (1 : SquareFree I) := by
  simp [scalar]

omit [DecidableEq I] in
theorem scalar_add (a b : ℂ) : scalar (a + b) = (scalar a + scalar b : SquareFree I) := by
  simp [scalar]

omit [DecidableEq I] in
theorem scalar_mul (a b : ℂ) : scalar (a * b) = (scalar a * scalar b : SquareFree I) := by
  simp [scalar]

omit [DecidableEq I] in
theorem scalar_sum {T : Type*} (s : Finset T) (f : T → ℂ) :
    scalar (∑ i ∈ s, f i) = (∑ i ∈ s, scalar (f i) : SquareFree I) := by
  simp [scalar]

omit [DecidableEq I] in
theorem scalar_prod {T : Type*} (s : Finset T) (f : T → ℂ) :
    scalar (∏ i ∈ s, f i) = (∏ i ∈ s, scalar (f i) : SquareFree I) := by
  simp [scalar]

omit [DecidableEq I] in
@[simp] theorem variable_sq (i : I) : rowVariable i ^ 2 = (0 : SquareFree I) := by
  rw [rowVariable, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

omit [DecidableEq I] in
@[simp] theorem variable_mul_self (i : I) : rowVariable i * rowVariable i = (0 : SquareFree I) := by
  simpa only [pow_two] using variable_sq i

omit [DecidableEq I] in
@[simp] theorem monomial_empty : monomial (∅ : Finset I) = (1 : SquareFree I) := by
  simp [monomial]

theorem variable_monomial_erase (s : Finset I) {i : I} (hi : i ∈ s) :
    rowVariable i * monomial (s.erase i) = monomial s := by
  exact Finset.mul_prod_erase s rowVariable hi

theorem variable_monomial_zero (s : Finset I) {i : I} (hi : i ∈ s) :
    rowVariable i * monomial s = (0 : SquareFree I) := by
  rw [← variable_monomial_erase s hi, ← mul_assoc, variable_mul_self, zero_mul]

theorem monomial_union (s t : Finset I) (h : Disjoint s t) :
    monomial (s ∪ t) = monomial s * monomial t := by
  exact Finset.prod_union h

theorem variable_rooted (s : Finset I) (c : I → ℂ) {i : I} (hi : i ∈ s) :
    rowVariable i * rooted s c = scalar (c i) * monomial s := by
  unfold rooted
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · rw [mul_left_comm, variable_monomial_erase s hi]
  · intro j hj hji
    have hij : i ∈ s.erase j := Finset.mem_erase.mpr ⟨Ne.symm hji, hi⟩
    rw [mul_left_comm, variable_monomial_zero (s.erase j) hij, mul_zero]
  · exact fun h => False.elim (h hi)

theorem internal_edge_rooted (s : Finset I) (c : I → ℂ) {i j : I}
    (hi : i ∈ s) (hj : j ∈ s) (u v : ℂ) :
    (scalar u * rowVariable i + scalar v * rowVariable j) * rooted s c =
      scalar (u * c i + v * c j) * monomial s := by
  rw [add_mul, mul_assoc, mul_assoc, variable_rooted s c hi,
    variable_rooted s c hj, ← mul_assoc, ← mul_assoc,
    ← scalar_mul, ← scalar_mul, ← add_mul, ← scalar_add]

theorem internal_edge_monomial (s : Finset I) {i j : I}
    (hi : i ∈ s) (hj : j ∈ s) (u v : ℂ) :
    (scalar u * rowVariable i + scalar v * rowVariable j) * monomial s =
      (0 : SquareFree I) := by
  rw [add_mul, mul_assoc, mul_assoc, variable_monomial_zero s hi,
    variable_monomial_zero s hj, mul_zero, mul_zero, add_zero]

end ResearchMain.Chollet.RankCoefficients
