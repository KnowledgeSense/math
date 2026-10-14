import BuchweitzProfiles

open BuchweitzProfiles

/-- The public result retains the whole arbitrary input sequence and all tail orders. -/
example (N L : Nat) (a : Nat → Int) (hN : 2 ≤ N) (hL : 1 ≤ L)
    (ha : ∀ n, 2 ≤ n → n ≤ N → -(L : Int) ≤ a n ∧ a n ≤ L) :
    ∃ S : NumericalSemigroup, ∃ G : Finset Nat,
      IsMultiplicity S (profileMultiplicity N L) ∧
      IsConductor S (2 * profileMultiplicity N L) ∧
      (∀ n, n ∈ G ↔ n ∉ S) ∧ G.card = profileGenus N L ∧
      (∀ n, 2 ≤ n → n ≤ N → beta G n = a n) ∧
      (∀ n, N < n → beta G n < 0) :=
  prescribed_buchweitz_profile N L a hN hL ha

example : profileMultiplicity 2 1 = 1441 := by decide
example : profileGenus 2 1 = 1459 := by decide

/-- A zero input is included without a special nonzero-profile assumption. -/
example : ∃ S : NumericalSemigroup, ∃ G : Finset Nat,
    IsMultiplicity S 1441 ∧ IsConductor S 2882 ∧
    (∀ n, n ∈ G ↔ n ∉ S) ∧ G.card = 1459 ∧
    (∀ n, 2 ≤ n → n ≤ 2 → beta G n = 0) ∧
    (∀ n, 2 < n → beta G n < 0) := by
  simpa [profileMultiplicity, profileGenus] using
    prescribed_buchweitz_profile 2 1 (fun _ => 0) (by decide) (by decide)
      (by intro n _ _; constructor <;> decide)

example : IsMultiplicity exampleSemigroup 169 := example_multiplicity
example : IsConductor exampleSemigroup 338 := example_conductor
example : exampleG.card = 172 := example_genus
example (n : Nat) : (2 ≤ n ∧ 0 < beta exampleG n) ↔ n = 3 ∨ n = 6 :=
  example_buchweitz_set n

#print axioms BuchweitzProfiles.prescribed_buchweitz_profile
#print axioms BuchweitzProfiles.example_buchweitz_set
