import ASR312.SquarePivotCounting
import Mathlib.Combinatorics.Enumerative.Schroder

namespace ASR312

 theorem squareASMCount_le_succ (n : ℕ) : squareASMCount n ≤ squareASMCount (n+1) := by
  have he := zeroCorner_card_add n
  omega

 theorem squareASMCount_recurrence (n : ℕ) :
    squareASMCount (n+1) = squareASMCount n +
      ∑ i : Fin n, squareASMCount (i.val+1) * squareASMCount (n-i.val) := by
  rw [squareASMCount_pivot_sum,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Nat.sub_zero,squareASMCount_zero,one_mul,negativeAt_card_zero,Nat.add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [negativeAt_card i.succ (by simp)]
  simp only [Fin.val_succ]
  have hlarge : n+1-(i.val+1) = (n-(i.val+1))+1 := by omega
  have hlarge' : n-i.val = (n-(i.val+1))+1 := by omega
  rw [hlarge,hlarge',← Nat.mul_add]
  congr 1
  have hm := squareASMCount_le_succ (n-(i.val+1))
  omega

 theorem squareASMCount_one : squareASMCount 1 = 1 := by
  simpa [squareASMCount_zero] using squareASMCount_recurrence 0

 theorem squareASMCount_eq_schroder (n : ℕ) : squareASMCount (n+1) = Nat.largeSchroder n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using squareASMCount_one
    | succ n =>
      rw [squareASMCount_recurrence,Nat.largeSchroder,ih n (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [ih i.val (by omega)]
      have he : n+1-i.val = (n-i.val)+1 := by omega
      rw [he,ih (n-i.val) (by omega)]

 theorem S_square_schroder (n : ℕ) : S (n+1) (n+1) (n+1) = Nat.largeSchroder n := by
  rw [S_square,squareASMCount_eq_schroder]

end ASR312
