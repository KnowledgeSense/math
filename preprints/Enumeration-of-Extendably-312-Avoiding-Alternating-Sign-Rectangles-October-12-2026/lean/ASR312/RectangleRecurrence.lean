import ASR312.RectanglePivotCardinals

namespace ASR312

/-- The common row-complete and interior recurrence, directly for the original
existential-extension count. The missing balanced-width face is separate. -/
theorem S_pivot_recurrence (r k d : ℕ) (hdr : d+1 ≤ r) (hdk : d+1 ≤ k+1)
    (hface : d+1 < k+1 ∨ r ≤ k+1) :
    S r (k+1) (d+1) = S r k (d+1) + S (r-1) k d +
      ∑ p : Fin d, Nat.largeSchroder p.val *
        (S (r-(p.val+1)) (k+1-(p.val+1)) (d+1-(p.val+1)) -
          (r-(p.val+1)-1).choose (d+1-(p.val+1))) := by
  rw [rectangle_pivot_count_sum r k (d+1) hdr hdk hface,Fin.sum_univ_succ]
  have hp0 : (Fin.castLE hdr (0 : Fin (d+1))).val = 0 := rfl
  have hpc : (Fin.castLE hdr (0 : Fin (d+1))).val < d+1 := by simp
  have hpw : (Fin.castLE hdr (0 : Fin (d+1))).val < k+1 := by simp
  rw [pureAtRectangle_card _ hpc hpw,negativeAtRectangle_card_zero _ hp0,
    hp0,squareASMCount_zero,one_mul]
  simp only [Nat.add_zero,Nat.zero_add,Nat.add_sub_cancel_right]
  rw [← Nat.add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [rectangle_pivot_pair_card _ (by simp) (by simp) hdk]
  simp only [Fin.val_castLE,Fin.val_succ,squareASMCount_eq_schroder]

/-- Proposition 4.2, in a successor-indexed finite-sum form. -/
theorem S_row_complete_recurrence (r k : ℕ) (hrk : r+1 ≤ k+1) :
    S (r+1) (k+1) (r+1) = S (r+1) k (r+1) + S r k r +
      ∑ p : Fin r, Nat.largeSchroder p.val *
        S (r+1-(p.val+1)) (k+1-(p.val+1)) (r+1-(p.val+1)) := by
  rw [S_pivot_recurrence (r+1) k r le_rfl hrk (Or.inr hrk)]
  simp only [Nat.add_sub_cancel_right]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  have hzero : (r+1-(p.val+1)-1).choose (r+1-(p.val+1)) = 0 := by
    apply Nat.choose_eq_zero_of_lt
    have hp := p.isLt
    omega
  rw [hzero,Nat.sub_zero]

/-- Theorem 4.4 on its stated interior range, with its binomial correction. -/
theorem S_interior_recurrence (r k d : ℕ) (hdr : d+1 < r) (hdk : d+1 < k+1) :
    S r (k+1) (d+1) = S r k (d+1) + S (r-1) k d +
      ∑ p : Fin d, Nat.largeSchroder p.val *
        (S (r-(p.val+1)) (k+1-(p.val+1)) (d+1-(p.val+1)) -
          (r-(p.val+1)-1).choose (d+1-(p.val+1))) :=
  S_pivot_recurrence r k d hdr.le hdk.le (Or.inl hdk)

end ASR312
