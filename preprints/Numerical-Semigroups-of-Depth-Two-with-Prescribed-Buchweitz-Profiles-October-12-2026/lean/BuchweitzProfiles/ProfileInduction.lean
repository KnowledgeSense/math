import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BuchweitzProfiles

/-- Discrete integration on the prescribed finite range. -/
theorem profile_from_differences (B a : Nat → Int) (N : Nat)
    (hfirst : B 1 = a 1)
    (hstep : ∀ n, 2 ≤ n → n ≤ N → B n - B (n - 1) = a n - a (n - 1)) :
    ∀ n, 1 ≤ n → n ≤ N → B n = a n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro _; exact hfirst
  | succ n hn ih =>
    intro hnN
    have hp := ih (by omega)
    have hs := hstep (n + 1) (by omega) hnN
    simpa only [Nat.add_sub_cancel] using (show B (n + 1) = a (n + 1) by
      simp only [Nat.add_sub_cancel] at hs
      omega)

/-- Once negative, a strictly decreasing tail stays negative. -/
theorem negative_tail (B : Nat → Int) (N : Nat)
    (hfirst : B (N + 1) < 0)
    (hstep : ∀ n, N + 2 ≤ n → B n < B (n - 1)) :
    ∀ n, N < n → B n < 0 := by
  intro n hn
  have hstart : N + 1 ≤ n := by omega
  induction n, hstart using Nat.le_induction with
  | base => exact hfirst
  | succ n hn ih =>
    have hs := hstep (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hs
    omega

/-- The final discrete argument of Section 5. This is an auxiliary result on
integer sequences; construction of the semigroup and its sumset counts is separate. -/
theorem prescribed_profile_from_steps (B a : Nat → Int) (N K : Nat) (L h : Int)
    (hN : 2 ≤ N) (hL : 1 ≤ L) (_hNK : N + 1 ≤ K)
    (hlarge : L + (N : Int) < h) (hK : 2 * (K : Int) + 1 < 2 * (h + 3))
    (haN : a N ≤ L) (hfirst : B 1 = a 1)
    (hstep : ∀ n, 2 ≤ n → n ≤ N → B n - B (n - 1) = a n - a (n - 1))
    (hnext : B (N + 1) - B N = 2 * (N : Int) + 3 - 2 * (h + 3))
    (hmiddle : ∀ n, N + 2 ≤ n → n ≤ K →
      B n - B (n - 1) = 2 * (n : Int) + 1 - 2 * (h + 3))
    (hfinal : ∀ n, K < n → B n - B (n - 1) = -2 * (h + 3)) :
    (∀ n, 1 ≤ n → n ≤ N → B n = a n) ∧ (∀ n, N < n → B n < 0) := by
  have heq := profile_from_differences B a N hfirst hstep
  refine ⟨heq, negative_tail B N ?_ ?_⟩
  · have heqN := heq N (by omega) (by omega)
    omega
  · intro n hn
    by_cases hnK : n ≤ K
    · have hs := hmiddle n hn hnK
      have hnK' : (n : Int) ≤ (K : Int) := by omega
      omega
    · have hs := hfinal n (by omega)
      omega

end BuchweitzProfiles
