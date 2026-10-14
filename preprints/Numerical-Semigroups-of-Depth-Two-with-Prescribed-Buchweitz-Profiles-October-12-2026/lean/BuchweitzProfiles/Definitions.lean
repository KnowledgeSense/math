import Std

/-! Numerical semigroups represented by their actual subsets of the natural numbers. -/
namespace BuchweitzProfiles

/-- An additive submonoid of the natural numbers with finite complement,
expressed by the equivalent eventual-membership condition. -/
structure NumericalSemigroup where
  carrier : Nat → Prop
  zero_mem : carrier 0
  add_mem : ∀ {a b}, carrier a → carrier b → carrier (a + b)
  cofinite : ∃ c, ∀ n, c ≤ n → carrier n

instance : Membership Nat NumericalSemigroup := ⟨fun S n => S.carrier n⟩

/-- The least positive member of the semigroup. -/
def IsMultiplicity (S : NumericalSemigroup) (m : Nat) : Prop :=
  0 < m ∧ m ∈ S ∧ ∀ n, n ∈ S → 0 < n → m ≤ n

/-- The first integer from which all integers belong to the semigroup. -/
def IsConductor (S : NumericalSemigroup) (c : Nat) : Prop :=
  (∀ n, c ≤ n → n ∈ S) ∧ ∀ d, (∀ n, d ≤ n → n ∈ S) → c ≤ d

/-- The precise gapset in Lemma 2.1 of the release paper. -/
def ReflectedGap (m : Nat) (C : Nat → Prop) (n : Nat) : Prop :=
  (1 ≤ n ∧ n < m) ∨ ∃ c, C c ∧ n + c = 2 * m - 1

end BuchweitzProfiles
