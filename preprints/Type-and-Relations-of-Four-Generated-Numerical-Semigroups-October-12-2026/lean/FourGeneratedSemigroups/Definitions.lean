import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section

namespace FourGeneratedSemigroups

/-- A numerical semigroup is an additive submonoid of the natural numbers
with finite complement. -/
structure NumericalSemigroup where
  monoid : AddSubmonoid ℕ
  finite_complement : (monoid : Set ℕ)ᶜ.Finite

namespace NumericalSemigroup

/-- Membership after embedding the semigroup in the integers. -/
def memInt (S : NumericalSemigroup) (z : ℤ) : Prop :=
  ∃ n : ℕ, z = (n : ℤ) ∧ n ∈ S.monoid

/-- The actual pseudo-Frobenius numbers, including the integer convention. -/
def pseudoFrobenius (S : NumericalSemigroup) : Set ℤ :=
  {f | ¬ S.memInt f ∧ ∀ n ∈ S.monoid, n ≠ 0 → S.memInt (f + (n : ℤ))}

/-- The Apéry set with respect to a positive member of the semigroup. -/
def apery (S : NumericalSemigroup) (d : ℕ) : Set ℤ :=
  {w | S.memInt w ∧ ¬ S.memInt (w - (d : ℤ))}

/-- Maximality in the semigroup order, expressed by addition of nonzero members. -/
def maximalApery (S : NumericalSemigroup) (d : ℕ) : Set ℤ :=
  {w | w ∈ S.apery d ∧ ∀ n ∈ S.monoid, n ≠ 0 → w + (n : ℤ) ∉ S.apery d}

/-- The type is the cardinality of the actual pseudo-Frobenius set. -/
noncomputable def type (S : NumericalSemigroup) : ℕ := Nat.card S.pseudoFrobenius

end NumericalSemigroup

abbrev Factorization := Fin 4 →₀ ℕ

/-- The four-generator factorization map. -/
def factorizationMap (d : Fin 4 → ℕ) : Factorization →+ ℕ where
  toFun c := ∑ i, c i * d i
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]

/-- A specified minimal generating set of cardinality four. -/
structure FourGenerated (S : NumericalSemigroup) where
  generators : Fin 4 → ℕ
  positive : ∀ i, 0 < generators i
  generates : ∀ n, n ∈ S.monoid ↔ ∃ c, factorizationMap generators c = n
  minimal : ∀ i, ¬ ∃ c : Factorization,
    c i = 0 ∧ factorizationMap generators c = generators i

/-- Relations in the actual factorization congruence. -/
def factorizationCongruence (d : Fin 4 → ℕ) : AddCon Factorization :=
  AddCon.ker (factorizationMap d)

/-- A finite presentation generates exactly the factorization congruence. -/
def IsPresentation (d : Fin 4 → ℕ) (R : Finset (Factorization × Factorization)) : Prop :=
  addConGen (fun a b => (a,b) ∈ R) = factorizationCongruence d

/-- Minimality is inclusion-minimality among presentations. -/
def IsMinimalPresentation (d : Fin 4 → ℕ) (R : Finset (Factorization × Factorization)) : Prop :=
  IsPresentation d R ∧ ∀ R' ⊂ R, ¬ IsPresentation d R'

end FourGeneratedSemigroups
