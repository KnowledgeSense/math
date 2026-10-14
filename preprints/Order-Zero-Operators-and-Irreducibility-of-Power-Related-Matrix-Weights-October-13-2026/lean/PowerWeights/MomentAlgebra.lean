import PowerWeights.Definitions

namespace PowerWeights

/-- The triangular orthogonality relations propagate an intertwining identity
from the zeroth moment to all moments. This is purely finite algebra. -/
theorem moments_intertwine {R : Type*} [Ring R] (M : ℕ → R)
    (L : ℕ → ℕ → R) (C D : R)
    (hzero : C * M 0 = M 0 * D)
    (horth : ∀ n, 0 < n → M n = -∑ j ∈ Finset.range n, L n j * M j)
    (hcomm : ∀ n j, j < n → C * L n j = L n j * C) :
    ∀ n, C * M n = M n * D := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · simpa [hn] using hzero
    · rw [horth n (Nat.pos_of_ne_zero hn), mul_neg, neg_mul,
        Finset.mul_sum, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [← mul_assoc, hcomm n j hj', mul_assoc, ih j hj', ← mul_assoc]

end PowerWeights
