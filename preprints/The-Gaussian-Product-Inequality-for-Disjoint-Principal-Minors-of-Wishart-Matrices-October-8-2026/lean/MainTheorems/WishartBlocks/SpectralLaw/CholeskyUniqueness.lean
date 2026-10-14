import MainTheorems.WishartBlocks.SpectralLaw.CholeskyExistence

namespace ResearchMain.WishartBlocks

open scoped BigOperators

theorem lowerGram_entry {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : L.IsLowerTriangular) (i j : Fin n) :
    (L * L.transpose) i j = L i j * L j j +
      ∑ k : Fin n, if k < j then L i k * L j k else 0 := by
  rw [Matrix.mul_apply]
  have hs : (∑ k : Fin n, L i k * L j k) =
      ∑ k : Fin n, ((if k = j then L i j * L j j else 0) +
        (if k < j then L i k * L j k else 0)) := by
    apply Finset.sum_congr rfl
    intro k _
    rcases lt_trichotomy k j with h | rfl | h
    · simp only [ne_of_lt h, h, ite_false, ite_true, zero_add]
    · simp only [lt_self_iff_false, ite_false, ite_true, add_zero]
    · simp only [ne_of_gt h, not_lt_of_gt h, ite_false,
        hL h, mul_zero, zero_add]
  change (∑ k : Fin n, L i k * L j k) = _
  rw [hs, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem lowerGram_injective_positive {n : ℕ}
    {L M : Matrix (Fin n) (Fin n) ℝ}
    (hL : L.IsLowerTriangular) (hM : M.IsLowerTriangular)
    (hLpos : ∀ i, 0 < L i i) (hMpos : ∀ i, 0 < M i i)
    (hGram : L * L.transpose = M * M.transpose) : L = M := by
  have heq : ∀ e : LowerIndex n, L e.val.1 e.val.2 = M e.val.1 e.val.2 := by
    intro e
    refine wellFounded_lt.induction
      (C := fun e : LowerIndex n => L e.val.1 e.val.2 = M e.val.1 e.val.2) e ?_
    intro e ih
    have htail :
        (∑ k : Fin n, if k < e.val.2 then L e.val.1 k * L e.val.2 k else 0) =
        ∑ k : Fin n, if k < e.val.2 then M e.val.1 k * M e.val.2 k else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k < e.val.2
      · rw [ite_eq_left hk, ite_eq_left hk]
        have hfirst : L e.val.1 k = M e.val.1 k :=
          ih ⟨toLex (e.val.1, k), hk.le.trans e.property⟩ (by
            change (toLex (e.val.1, k) : Fin n ×ₗ Fin n) < e.val
            exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hk⟩))
        have hsecond : L e.val.2 k = M e.val.2 k :=
          ih ⟨toLex (e.val.2, k), hk.le⟩ (by
            change (toLex (e.val.2, k) : Fin n ×ₗ Fin n) < e.val
            rcases lt_or_eq_of_le e.property with h | h
            · exact Prod.Lex.lt_iff.mpr (Or.inl h)
            · exact Prod.Lex.lt_iff.mpr (Or.inr ⟨h, hk⟩))
        rw [hfirst, hsecond]
      · simp only [hk, ite_false]
    have hentry := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ =>
      A e.val.1 e.val.2) hGram
    rw [lowerGram_entry hL, lowerGram_entry hM, htail] at hentry
    have hproduct : L e.val.1 e.val.2 * L e.val.2 e.val.2 =
        M e.val.1 e.val.2 * M e.val.2 e.val.2 := add_right_cancel hentry
    by_cases hd : e.val.1 = e.val.2
    · rw [hd] at hproduct ⊢
      nlinarith [hLpos e.val.2, hMpos e.val.2]
    · have hj : e.val.2 < e.val.1 := lt_of_le_of_ne e.property (Ne.symm hd)
      have hdj : L e.val.2 e.val.2 = M e.val.2 e.val.2 :=
        ih ⟨toLex (e.val.2, e.val.2), le_rfl⟩ (by
          change (toLex (e.val.2, e.val.2) : Fin n ×ₗ Fin n) < e.val
          exact Prod.Lex.lt_iff.mpr (Or.inl hj))
      rw [hdj] at hproduct
      exact (mul_right_cancel₀ (hMpos e.val.2).ne') hproduct
  ext i j
  by_cases hij : j ≤ i
  · exact heq ⟨toLex (i, j), hij⟩
  · rw [hL (lt_of_not_ge hij), hM (lt_of_not_ge hij)]

theorem choleskyCoordinates_injOn_positive {n : ℕ} :
    Set.InjOn (choleskyCoordinates (n := n))
      {x | ∀ i : Fin n, 0 < lowerMatrix x i i} := by
  intro x hx y hy hxy
  have hGram : lowerMatrix x * (lowerMatrix x).transpose =
      lowerMatrix y * (lowerMatrix y).transpose := by
    have h := congrArg symmetricMatrix hxy
    simpa only [symmetricMatrix_choleskyCoordinates] using h
  have hL := lowerGram_injective_positive (lowerMatrix_lowerTriangular x)
    (lowerMatrix_lowerTriangular y) hx hy hGram
  funext e
  simpa only [lowerMatrix_entry] using congrArg
    (fun L : Matrix (Fin n) (Fin n) ℝ => L e.val.1 e.val.2) hL

end ResearchMain.WishartBlocks
