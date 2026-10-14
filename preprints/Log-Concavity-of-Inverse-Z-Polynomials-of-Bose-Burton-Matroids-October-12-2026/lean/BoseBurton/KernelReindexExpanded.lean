import BoseBurton.KernelReindexFinite
import BoseBurton.OriginalKernel

noncomputable section
namespace BoseBurton
open Finset Polynomial

theorem kernel_reindex_expanded (q : ℝ) (r s : ℕ) (hsr : s≤r) :
    (∑ d∈Icc 1 r,∑ i∈range (d+1),
      C ((-1:ℝ)^d*gaussian q s (max i (d-i))*
        gaussian q (r-max i (d-i)) (d-max i (d-i)))*X^i*projectiveRow q (r-d))=
    ∑ h∈Icc 1 s,∑ l∈range (min h (r-h)+1),
      C ((-1:ℝ)^(h+l)*gaussian q s h*gaussian q (r-h) l)*
        orientationPolynomial h l*projectiveRow q (r-h-l) := by
  rw [triangular_sum_reindex]
  have he : (∑ h∈Icc 1 r,∑ l∈range (min h (r-h)+1),
      (C ((-1:ℝ)^(h+l)*gaussian q s (max l (h+l-l))*
        gaussian q (r-max l (h+l-l)) (h+l-max l (h+l-l)))*X^l*projectiveRow q (r-(h+l))+
      if l<h then C ((-1:ℝ)^(h+l)*gaussian q s (max h (h+l-h))*
        gaussian q (r-max h (h+l-h)) (h+l-max h (h+l-h)))*X^h*projectiveRow q (r-(h+l)) else 0))=
      ∑ h∈Icc 1 r,∑ l∈range (min h (r-h)+1),
        C ((-1:ℝ)^(h+l)*gaussian q s h*gaussian q (r-h) l)*
          orientationPolynomial h l*projectiveRow q (r-h-l) := by
    apply sum_congr rfl
    intro h _
    apply sum_congr rfl
    intro l hl
    have hlh : l≤h := by simp only [mem_range] at hl; omega
    rw [show h+l-l=h by omega,show h+l-h=l by omega,
      max_eq_right hlh,max_eq_left hlh,show r-(h+l)=r-h-l by omega]
    simp only [Nat.add_sub_cancel_left]
    by_cases he : l<h
    · simp only [he,ite_true,orientationPolynomial]
      ring
    · have hleq : l=h := by omega
      subst l
      simp [orientationPolynomial]
  rw [he]
  symm
  apply sum_subset (Icc_subset_Icc le_rfl hsr)
  intro h hh hnot
  have hhs : s<h := by simp only [mem_Icc] at hh hnot; omega
  apply sum_eq_zero
  intro l _
  simp [gaussian_outside q s h hhs]

end BoseBurton
