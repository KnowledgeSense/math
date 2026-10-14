import Paving.ActualMixturePayment

noncomputable section
open Finset
namespace Paving
variable {α : Type*} [Fintype α]

def actualLowerMixture (M : Matroid α) (i : ℕ) : ℝ :=
  ∑j:MixtureIndex M,actualWeight M j*lowerComponent (rank M) M.E.ncard (actualParameter M j) i

def actualEvenMixture (M : Matroid α) (m i : ℕ) : ℝ :=
  if i=m then actualLowerMixture M (m-1)+middleIncrement (middleBinomial m) ((M.E.ncard:ℝ)-m) m
  else actualLowerMixture M (min i (2*m-i))

theorem IsPaving.actualLower_positive {M : Matroid α} (hM : IsPaving M) (i : ℕ)
    (hi : i+1 < rank M) : 0 < actualLowerMixture M i := by
  apply mixture_positive univ (actualWeight M) _
    (fun j _ => hM.actualWeight_nonneg (by omega) j) (actualWeight_sum M)
  intro j _
  exact lowerComponent_positive (actualParameter M j) hi (rank_le_ground_card M) (actualParameter_valid M j)

theorem IsPaving.actual_odd_positive {M : Matroid α} (hM : IsPaving M)
    (m : ℕ) (hm : 1 ≤ m) (hr : rank M=2*m+1) (i : ℕ) :
    0 < actualReflectedMixture M i := by
  change 0 < actualLowerMixture M (min i (rank M-i))
  apply hM.actualLower_positive
  have : min i (rank M-i) ≤ m := by omega
  omega

theorem actualReflectedMixture_symm (M : Matroid α) (i : ℕ) (hi : i ≤ rank M) :
    actualReflectedMixture M (rank M-i)=actualReflectedMixture M i :=
  reflectedMixture_symm _ _ _ _ _ _ hi

theorem IsPaving.actual_even_positive {M : Matroid α} (hM : IsPaving M)
    (m : ℕ) (hm : 2 ≤ m) (hr : rank M=2*m) (i : ℕ) (hi : i ≤ 2*m) :
    0 < actualEvenMixture M m i := by
  have hn : 2*m ≤ M.E.ncard := hr ▸ rank_le_ground_card M
  have hnR : (2:ℝ)*m ≤ M.E.ncard := by exact_mod_cast hn
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  unfold actualEvenMixture
  split_ifs with he
  · exact add_pos (hM.actualLower_positive _ (by omega))
      (middleIncrement_positive (middleBinomial_positive (by omega)) hmR (by linarith))
  · apply hM.actualLower_positive
    have : min i (2*m-i) ≤ m := by omega
    omega

theorem actualEvenMixture_symm (M : Matroid α) (m i : ℕ) (hi : i ≤ 2*m) :
    actualEvenMixture M m (2*m-i)=actualEvenMixture M m i := by
  have he : 2*m-i=m ↔ i=m := by omega
  unfold actualEvenMixture
  simp only [he,Nat.sub_sub_self hi,min_comm]

theorem IsPaving.actual_even_strict {M : Matroid α} (hM : IsPaving M)
    (m : ℕ) (hm : 2 ≤ m) (hr : rank M=2*m) :
    ∀i,1 ≤ i → i < 2*m → actualEvenMixture M m (i-1)*actualEvenMixture M m (i+1) <
      actualEvenMixture M m i^2 := by
  have hn : 2*m ≤ M.E.ncard := hr ▸ rank_le_ground_card M
  have hnR : (2:ℝ)*m ≤ M.E.ncard := by exact_mod_cast hn
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hl (i : ℕ) (hi : i < m) : actualEvenMixture M m i=actualLowerMixture M i := by
    simp only [actualEvenMixture,ite_eq_right (by omega : i≠m),min_eq_left (by omega : i ≤ 2*m-i)]
  apply even_row_strict _ m M.E.ncard hm hn
  · exact hM.actual_even_positive m hm hr
  · exact actualEvenMixture_symm M m
  · intro i hi him
    rw [hl i him,hl (i-1) (by omega)]
    unfold actualLowerMixture
    apply mixture_linear_bounds univ (actualWeight M) _ _ _ _
      (fun j _ => hM.actualWeight_nonneg (by omega) j)
    · intro j _
      simpa only [hr,Nat.cast_mul,Nat.cast_ofNat] using
        (lowerComponent_bounds (actualParameter M j) hi (by omega) (rank_le_ground_card M)
          (actualParameter_valid M j)).1
    · intro j _
      simpa only [hr,Nat.cast_mul,Nat.cast_ofNat] using
        (lowerComponent_bounds (actualParameter M j) hi (by omega) (rank_le_ground_card M)
          (actualParameter_valid M j)).2
  · rw [hl (m-2) (by omega),hl (m-1) (by omega)]
    simpa [actualEvenMixture,actualLowerMixture,hr] using
      hM.actual_penultimate_strict m hm hr
  · rw [hl (m-1) (by omega)]
    simp only [actualEvenMixture,ite_true,lt_add_iff_pos_right]
    exact middleIncrement_positive (middleBinomial_positive (by omega)) hmR (by linarith)

end Paving
