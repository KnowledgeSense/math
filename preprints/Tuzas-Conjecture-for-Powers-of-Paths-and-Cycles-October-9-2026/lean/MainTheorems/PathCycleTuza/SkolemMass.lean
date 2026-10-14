import MainTheorems.PathCycleTuza.SkolemPositions

namespace ResearchMain.PathCycleTuza

theorem positiveIndex_sum_twice (m : ℕ) :
    2 * (∑ i : Fin m, ((i.val : ℤ) + 1)) = (m : ℤ) * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem sum_Icc_twice (m : ℕ) :
    2 * (∑ i ∈ Finset.Icc 1 m, (i : ℤ)) = (m : ℤ) * (m + 1) := by
  rw [← positiveIndex_image m, Finset.sum_image]
  · simpa only [Nat.cast_add, Nat.cast_one] using positiveIndex_sum_twice m
  · intro i hi j hj h
    dsimp at h
    exact Fin.ext (by omega)

theorem skolemPositions_sum (m : ℕ) :
    (∑ i ∈ skolemPositions m (hookFlag m), (i : ℤ)) =
      2 * (m : ℤ) ^ 2 + m + hookFlag m := by
  by_cases h : hookFlag m = 1
  · have hm := hookFlag_positive m h
    have he : 2 * m ∈ Finset.Icc 1 (2 * m + 1) := by simp; omega
    have hs := Finset.sum_erase_add (Finset.Icc 1 (2 * m + 1)) (fun i : ℕ => (i : ℤ)) he
    have ht := sum_Icc_twice (2 * m + 1)
    simp only [skolemPositions, h, ite_true, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] at hs ht ⊢
    nlinarith
  · have hz : hookFlag m = 0 := by have := hookFlag_le_one m; omega
    have ht := sum_Icc_twice (2 * m)
    simp only [skolemPositions, hz, Nat.zero_ne_one, ite_false, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_zero, add_zero] at ht ⊢
    nlinarith

theorem SkolemData.endpoint_sum {m : ℕ} (D : SkolemData m (hookFlag m)) :
    (∑ p : Fin m × Bool, (D.endpoint p : ℤ)) =
      2 * (m : ℤ) ^ 2 + m + hookFlag m := by
  have h := skolemPositions_sum m
  rw [← D.endpoint_image, Finset.sum_image] at h
  · exact h
  · intro i hi j hj he
    exact D.endpoint_injective he

def SkolemData.maxDifference {m δ : ℕ} (D : SkolemData m δ) (i : Fin m) : ℕ :=
  m + D.lower i + i.val + 1

theorem SkolemData.difference_mass {m : ℕ} (D : SkolemData m (hookFlag m)) :
    4 * (∑ i : Fin m, (D.maxDifference i : ℤ)) =
      9 * (m : ℤ) ^ 2 + 3 * m + 2 * hookFlag m := by
  have he := D.endpoint_sum
  have hi := positiveIndex_sum_twice m
  have hs : (∑ p : Fin m × Bool, (D.endpoint p : ℤ)) =
      2 * (∑ i : Fin m, (D.lower i : ℤ)) + ∑ i : Fin m, ((i.val : ℤ) + 1) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Fintype.sum_bool, endpoint, Bool.false_eq_true, ite_false, ite_true,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hw : (∑ i : Fin m, (D.maxDifference i : ℤ)) =
      (m : ℤ) ^ 2 + (∑ i : Fin m, (D.lower i : ℤ)) + ∑ i : Fin m, ((i.val : ℤ) + 1) := by
    simp only [maxDifference, Nat.cast_add, Nat.cast_one]
    simp_rw [add_assoc]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp [pow_two]
  nlinarith

end ResearchMain.PathCycleTuza
