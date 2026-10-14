import BoseBurton.PartialNormalization
import BoseBurton.PositiveExpansionTelescoping

noncomputable section
namespace BoseBurton
open Finset Polynomial

theorem sum_Icc_one_eq_range (f : ℕ→ℝ) (s : ℕ) :
    (∑ h∈Icc 1 s,f h)=∑ i∈range s,f (i+1) := by
  symm
  apply sum_bij (fun i _=>i+1)
  · intro i hi
    simp only [mem_range] at hi
    simp only [mem_Icc]
    omega
  · intro i _ j _ hij
    omega
  · intro h hh
    simp only [mem_Icc] at hh
    refine ⟨h-1,?_,by omega⟩
    simp only [mem_range]
    omega
  · intro i _
    rfl

theorem signedKernel_eq_blocks (z : ℝ) (r s : ℕ) :
    signedKernel z r s=gaussianRow z r+∑ h∈Icc 1 s,kernelBlock z r s h := rfl

theorem signedKernel_coeff_internal (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s k : ℕ) (hsr : s<r) (hk : 1≤k) (hkr : k<r) :
    (signedKernel z r s).coeff k=scalarCoefficient z r s k := by
  have hg := (gaussian_pos z hz0 hz1 r k hkr.le).ne'
  have hdiv : (signedKernel z r s).coeff k/gaussian z r k=
      ∑ j∈range (s+1),positiveWeight z r s j*pairedProduct z r j k := by
    rw [signedKernel_eq_blocks,coeff_add,gaussianRow_coeff,finsetSum_coeff,add_div,div_self hg,sum_div]
    have he : (∑ h∈Icc 1 s,(kernelBlock z r s h).coeff k/gaussian z r k)=
        -(∑ h∈Icc 1 s,cancellationWeight z r s h*pairedProduct z r (h-1) k*
          cancellationBracket z r h k) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro h hh
      obtain ⟨hh1,hhs⟩ := mem_Icc.mp hh
      rw [kernelBlock_coeff_partials z hz0 hz1 r s h k hsr hh1 (by omega) hk hkr,
        partial_difference_normalized z hz0 hz1 r s h k hsr hh1 hk hkr]
      ring
    rw [he,sum_Icc_one_eq_range]
    simp only [Nat.add_sub_cancel]
    simpa only [sub_eq_add_neg] using cancellation_sum_eq_positive z hz0 hz1 r s k hsr hk hkr
  rw [scalarCoefficient,normalizedCoefficient,ite_eq_right (by omega)]
  exact (div_eq_iff hg).mp hdiv |>.trans (mul_comm _ _)

end BoseBurton
