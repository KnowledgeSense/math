import BoseBurton.EndpointProducts
import BoseBurton.WeightRatios
import BoseBurton.PairedConcavity

noncomputable section
namespace BoseBurton
open Finset

theorem positiveExpansion_one (z : ℝ) (r s : ℕ) :
    (∑ j∈range (s+1),positiveWeight z r s j*pairedProduct z r j 1)=positiveWeight z r s 0 := by
  rw [sum_eq_single 0]
  · simp [pairedProduct_zero]
  · intro j _ hj
    rw [pairedProduct_eq_zero_left z r j 1 (by omega) (by omega),mul_zero]
  · simp

theorem positiveExpansion_two (z : ℝ) (r s : ℕ) (hs : 1≤s) :
    (∑ j∈range (s+1),positiveWeight z r s j*pairedProduct z r j 2)=
      positiveWeight z r s 0+positiveWeight z r s 1*pairedProduct z r 1 2 := by
  have h0 : 0∈range (s+1) := by simp
  rw [← sum_erase_add _ _ h0]
  rw [sum_eq_single 1]
  · simp [pairedProduct_zero,add_comm]
  · intro j hj hj1
    have hj0 := (mem_erase.mp hj).1
    rw [pairedProduct_eq_zero_left z r j 2 (by omega) (by omega),mul_zero]
  · simp; omega

theorem secondProduct (z : ℝ) (r : ℕ) (hr : 3≤r) :
    pairedProduct z r 1 2=(1-z)*(1-z^(r-3)) := by
  simp [pairedProduct,fallingProduct,show r-2-1=r-3 by omega]

theorem positiveExpansion_two_increment_ratio (z : ℝ) (hz0 : 0<z) (hz1 : z<1)
    (r s : ℕ) (hsr : s<r) (hs : 1≤s) (hr : 3≤r) :
    positiveWeight z r s 1*pairedProduct z r 1 2/positiveWeight z r s 0=
      z^(r-s+2)*(1-z^s)*(1-z^(r-3))/((1-z)*(1-z^(r-1))) := by
  rw [mul_div_right_comm,positiveWeight_step_ratio z hz0 hz1 r s 0 hsr (by omega),
    secondProduct z r hr]
  simp only [Nat.sub_zero,Nat.zero_add,pow_one]
  have h : 1-z≠0 := by linarith
  field_simp

end BoseBurton
