import BuchweitzProfiles.Reflection
import BuchweitzProfiles.CountDifferences
import BuchweitzProfiles.ProfileInduction

namespace BuchweitzProfiles

/-- Converts a proved exact sumset count and pair statistics into the profile
of the actual reflected gapset. This is the final bridge, not the existence
of the input finite set or of the pair statistics. -/
theorem profile_of_exact_row_count {ι : Type*} (J : Finset ι) (C : Finset Nat)
    (m N K h : Nat) (L : Int) (d t : ι → Nat) (a : Nat → Int)
    (hm : 3 ≤ m) (hC : ∀ c ∈ C, c ≤ m - 2) (hz : 0 ∈ C)
    (hpos : ∃ c ∈ C, 0 < c) (hcard : C.card = h + 4)
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hNK : N + 1 ≤ K)
    (hlarge : L + (N : Int) < h) (hK : 2 * (K : Int) + 1 < 2 * ((h : Int) + 3))
    (ha1 : a 1 = 1) (haN : a N ≤ L)
    (hd : ∀ j ∈ J, 2 ≤ d j ∧ d j ≤ N + 1)
    (ht : ∀ j ∈ J, d j = N + 1 → t j = 0)
    (hcount : ∀ n, 1 ≤ n → (truncatedCount C m n : Int) = rowCount J K d t n)
    (hstatistics : ∀ n, 2 ≤ n → n ≤ N →
      ((J.filter (fun j => n + 1 ≤ d j)).card : Int) * (2 * (n : Int) - 1) +
      ∑ j ∈ J.filter (fun j => n = d j), (t j : Int) =
        2 * (h : Int) + 5 - 2 * (n : Int) + a n - a (n - 1)) :
    (∀ n, 1 ≤ n → n ≤ N → beta (gapset m C) n = a n) ∧
    (∀ n, N < n → beta (gapset m C) n < 0) := by
  have hb (n : Nat) (hn : 1 ≤ n) :
      beta (gapset m C) n = rowCount J K d t n -
        (2 * (n : Int) - 1) * ((h : Int) + 3) := by
    rw [beta_gapset C m hm hC hz hpos n hn, hcount n hn, hcard]
    push_cast
    ring
  have hdiff (n : Nat) (hn : 2 ≤ n) :
      beta (gapset m C) n - beta (gapset m C) (n - 1) =
        rowCount J K d t n - rowCount J K d t (n - 1) - 2 * ((h : Int) + 3) := by
    rw [hb n (by omega), hb (n - 1) (by omega)]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  apply prescribed_profile_from_steps (beta (gapset m C)) a N K L (h : Int)
    hN hL hNK hlarge hK haN
  · rw [beta_one, ha1]
  · intro n hn hnN
    rw [hdiff n hn, rowCount_difference_statistics J K d t (fun j hj => (hd j hj).1) n hn]
    rw [ite_eq_left (by omega : n ≤ K)]
    have hs := hstatistics n hn hnN
    omega
  · have hn : 2 ≤ N + 1 := by omega
    have hs := hdiff (N + 1) hn
    rw [rowCount_tail_difference J K N d t hd ht (N + 1) (by omega) hn,
      ite_eq_left hNK] at hs
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hs
    linarith
  · intro n hn hnK
    rw [hdiff n (by omega), rowCount_tail_difference J K N d t hd ht n (by omega)
      (by omega), ite_eq_left hnK]
  · intro n hnK
    rw [hdiff n (by omega), rowCount_tail_difference J K N d t hd ht n (by omega)
      (by omega), ite_eq_right (by omega : ¬ n ≤ K), zero_sub]
    ring

end BuchweitzProfiles
