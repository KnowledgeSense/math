import BuchweitzProfiles.NatParameters
import BuchweitzProfiles.Pairs

/-! Pair data instantiated from the prescribed integer sequence. -/
namespace BuchweitzProfiles

/-- The actual finite pair list attached to the input sequence. -/
def prescribedPairs (N L : Nat) (a : ℤ → ℤ) : List (Nat × Nat) :=
  constructionPairs (natQuotient N L a) (natRemainder N L a) N

def prescribedD {N L : Nat} {a : ℤ → ℤ}
    (j : Fin (prescribedPairs N L a).length) : Nat :=
  (prescribedPairs N L a)[j.val].1

def prescribedT {N L : Nat} {a : ℤ → ℤ}
    (j : Fin (prescribedPairs N L a).length) : Nat :=
  (prescribedPairs N L a)[j.val].2

theorem prescribedPairs_length {N L : Nat} {a : ℤ → ℤ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (ha1 : a 1 = 1)
    (ha : ∀ k : ℤ, 1 ≤ k → k ≤ N → -(L:ℤ) ≤ a k ∧ a k ≤ L) :
    (prescribedPairs N L a).length = (N+1)^2+2*L*(N+1) := by
  unfold prescribedPairs
  rw [length_constructionPairs _ _ N (by omega)]
  · exact natQuotient_one N L a
  · intro i hi hiN
    exact natQuotient_decreasing hN hL ha1 ha hi hiN

theorem prescribedPairs_bounds {N L : Nat} {a : ℤ → ℤ}
    (hN : 2 ≤ N) (j : Fin (prescribedPairs N L a).length) :
    2 ≤ prescribedD j ∧ prescribedD j ≤ N+1 ∧
      prescribedT j ≤ 2*prescribedD j-2 ∧
      (prescribedD j=N+1 → prescribedT j=0) := by
  exact constructionPairs_bounds (natQuotient N L a) (natRemainder N L a) N hN
    (by intro n hn hnN; exact natRemainder_bounds N L a hn)
    (List.getElem_mem j.isLt)

/-- The exact finite-index statistics needed by the main profile induction. -/
theorem prescribedPairs_statistics {N L : Nat} {a : ℤ → ℤ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (ha1 : a 1 = 1)
    (ha : ∀ k : ℤ, 1 ≤ k → k ≤ N → -(L:ℤ) ≤ a k ∧ a k ≤ L)
    (n : Nat) (hn : 2 ≤ n) (hnN : n ≤ N) :
    ((Finset.univ.filter (fun j : Fin (prescribedPairs N L a).length =>
        n+1 ≤ prescribedD j)).card : ℤ) * (2*(n:ℤ)-1) +
      ∑ j ∈ Finset.univ.filter (fun j : Fin (prescribedPairs N L a).length => n=prescribedD j),
        (prescribedT j : ℤ) =
      2*((prescribedPairs N L a).length : ℤ)+5-2*(n:ℤ)+a n-a ((n-1:Nat):ℤ) := by
  have hs := constructionPairs_statistics (natQuotient N L a) (natRemainder N L a) N n
    (by intro i hi hiN; exact natQuotient_decreasing hN hL ha1 ha hi hiN) hn hnN
  calc
    _ = (2*(n:ℤ)-1)*(natQuotient N L a n : ℤ)+(natRemainder N L a n : ℤ) := hs
    _ = _ := by
      rw [nat_division_identity hN hL ha hn hnN, prescribedPairs_length hN hL ha1 ha]
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      simp only [Nat.cast_one]

end BuchweitzProfiles
