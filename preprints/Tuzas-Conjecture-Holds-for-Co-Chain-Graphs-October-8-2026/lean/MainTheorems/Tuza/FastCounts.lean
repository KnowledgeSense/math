import MainTheorems.Tuza.CompletePacking
import MainTheorems.Tuza.FactorCard

namespace ResearchMain.Tuza

def pairCount (n : ℕ) : ℕ := n * (n - 1) / 2

def fastCompleteCount (n : ℕ) : ℕ := (pairCount n - completeLeave n) / 3

def fastFanCount (c q : ℕ) : ℕ := q / 2 * min c (if q % 2 = 0 then q - 1 else q)

@[simp]
theorem pairCount_eq (n : ℕ) : pairCount n = n.choose 2 := (Nat.choose_two_right n).symm

@[simp]
theorem fastCompleteCount_eq (n : ℕ) : fastCompleteCount n = completeCount n := by
  simp only [fastCompleteCount, pairCount_eq, completeCount]

@[simp]
theorem fastFanCount_eq (c q : ℕ) : fastFanCount c q = fanCount c q := by
  simp only [fastFanCount, fanCount, Nat.even_iff]

end ResearchMain.Tuza
