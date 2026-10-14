import WeakClergyman.Separation

namespace WeakClergyman.AntiRecurrence

variable {k : ℕ} {a : Fin k → ℕ} (S : AntiRecurrence k a)
variable (hk : 2 ≤ k) (ha : ∀ j, 0 < a j)
include hk ha

 theorem block_rank_bound (m j : ℕ) (hj : j < k) :
    (valuesBelow S.A (S.B (m+j))).card ≤ (valuesBelow S.A (S.B m)).card + 1 := by
  let h := (valuesBelow S.A (S.B m)).card
  by_contra hn
  have hb := (rank_bracket S.A_strictMono (S.B m)).1
  have hb' : S.B m < S.A h := lt_of_le_of_ne hb (S.disjoint_values h m).symm
  have he : S.A (h+1) < S.B (m+j) :=
    (rank_bracket S.A_strictMono (S.B (m+j))).2 (h+1) (by dsimp [h] at *; omega)
  have hcl := card_valuesBelow_gt S.B_strictMono hb'
  have hcr := card_valuesBelow_le S.B_strictMono he.le
  have hr0 := S.complementary_rank_A h
  have hr1 := S.complementary_rank_A (h+1)
  have hsep := S.separation h
  have ht := WeakClergyman.AntiRecurrence.tau_lower ha
  have hbig : k < k * (∑ i : Fin k, a i) := by nlinarith
  omega

 theorem block_span (m j : ℕ) (hj : j < k) :
    S.B m + j ≤ S.B (m+j) ∧ S.B (m+j) ≤ S.B m + j + 1 := by
  constructor
  · have := S.B_strictMono.add_le_nat j m
    simpa [Nat.add_comm] using this
  · have := S.block_rank_bound hk ha m j hj
    have h0 := S.complementary_rank m
    have h1 := S.complementary_rank (m+j)
    omega

 theorem weighted_block_bounds (n : ℕ) :
    (∑ j : Fin k, a j) * S.B (k*n) +
      (∑ j : Fin k, a j * j.val) ≤ S.A n ∧
    S.A n ≤ (∑ j : Fin k, a j) * S.B (k*n) +
      (∑ j : Fin k, a j * j.val) + (∑ j : Fin k, a j) := by
  classical
  have hl : (∑ j : Fin k, a j * (S.B (k*n) + j.val)) ≤ S.A n := by
    rw [S.recurrence]
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_left _ (S.block_span hk ha (k*n) j.val j.isLt).1
  have hu : S.A n ≤ ∑ j : Fin k, a j * (S.B (k*n) + j.val + 1) := by
    rw [S.recurrence]
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_left _ (S.block_span hk ha (k*n) j.val j.isLt).2
  simpa [Nat.mul_add, Finset.sum_add_distrib, ← Finset.sum_mul] using And.intro hl hu

end WeakClergyman.AntiRecurrence
