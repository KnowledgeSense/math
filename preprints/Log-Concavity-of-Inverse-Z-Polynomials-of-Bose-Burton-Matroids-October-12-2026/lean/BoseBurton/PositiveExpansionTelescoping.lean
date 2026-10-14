import BoseBurton.WeightTelescoping
import BoseBurton.ProductTelescoping

noncomputable section
namespace BoseBurton
open Finset

theorem cancellation_sum_eq_positive (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s k : ℕ) (hsr : s<r) (hk : 1≤k) (hkr : k<r) :
    1-(∑ i∈range s,cancellationWeight z r s (i+1)*pairedProduct z r i k*
      cancellationBracket z r (i+1) k)=
    ∑ j∈range (s+1),positiveWeight z r s j*pairedProduct z r j k := by
  let F : ℕ→ℝ := fun j=>cancellationWeight z r s j*z^(2*j)*pairedProduct z r j k
  let G : ℕ→ℝ := fun j=>cancellationWeight z r s (j+1)*(1-z^(j+1))^2*pairedProduct z r j k
  have hweights : (∑ j∈range (s+1),positiveWeight z r s j*pairedProduct z r j k)=
      (∑ j∈range (s+1),F j)-(∑ j∈range (s+1),G j) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    rw [positiveWeight_telescoping z hz0 hz1 r s j hsr (by simp only [mem_range] at hj; omega)]
    dsimp [F,G]
    ring
  have hcancel : (∑ i∈range s,cancellationWeight z r s (i+1)*pairedProduct z r i k*
      cancellationBracket z r (i+1) k)=∑ i∈range s,(G i-F (i+1)) := by
    apply sum_congr rfl
    intro i _
    have h := pairedProduct_telescoping z r (i+1) k (by omega) hk hkr
    simp only [Nat.add_sub_cancel] at h
    dsimp [F,G]
    linear_combination cancellationWeight z r s (i+1)*h
  have hF0 : F 0=1 := by simp [F,cancellationWeight_zero z hz0 hz1,pairedProduct_zero]
  have hGs : G s=0 := by simp [G,cancellationWeight_outside z r s (s+1) (by omega)]
  have hF := sum_range_succ' F s
  have hG := sum_range_succ G s
  rw [hF0] at hF
  rw [hGs,add_zero] at hG
  rw [hweights,hcancel,sum_sub_distrib]
  linarith

end BoseBurton
