import ASR312.FirstEmptyRowPartition

namespace ASR312

/-- Proposition 4.3, including the harmless zero-width boundary, for the original
extendably avoiding rectangles. -/
theorem S_balanced_recurrence (r k : ℕ) (hkr : k < r) :
    S r k k = ∑ q : Fin (k+1), S q.val k q.val * (r-q.val-1).choose (k-q.val) := by
  classical
  have hh := Nat.card_congr (firstEmptyPartitionEquiv r k hkr)
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma] at hh
  change (∑ q : Fin (k+1), Fintype.card (FirstEmptyAt (k := k) (Fin.castLE hkr q))) = S r k k at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro q _
  have hc := firstEmptyAt_card (Fin.castLE hkr q) (show q.val ≤ k by omega)
  simpa only [Nat.card_eq_fintype_card,Fin.val_castLE] using hc

end ASR312
