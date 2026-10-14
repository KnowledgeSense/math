import BoseBurton.KernelBlocks

noncomputable section
namespace BoseBurton
open Finset Polynomial

theorem kernelBlock_coeff_partials (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s h k : ℕ) (hsr : s<r) (hh : 1≤h) (hhr : h<r) (hk : 1≤k) (hkr : k<r) :
    (kernelBlock z r s h).coeff k=upperPartialTerm z r s h k-lowerPartialTerm z r s h k := by
  have heu : h*(r-s)+h.choose 2+(h+1).choose 2=h*(r-s+h) := by
    have h := choose_pair_square h
    nlinarith
  have hel : h*(r-s)+h.choose 2+h.choose 2=h*(r-s+h-1) := by
    have he := twice_choose_two h hh
    have hx : r-s+h-1=(r-s)+(h-1) := by omega
    rw [hx]
    nlinarith
  have hu (a b : ℝ) :
      ((-1:ℝ)^h*z^(h*(r-s)+h.choose 2)*gaussian z s h)*
        ((-1:ℝ)^h*z^((h+1).choose 2)*a*b)=
      z^(h*(r-s+h))*gaussian z s h*a*b := by
    calc
      _ = ((-1:ℝ)^h*(-1)^h)*(z^(h*(r-s)+h.choose 2)*z^((h+1).choose 2))*gaussian z s h*a*b := by ring
      _ = _ := by rw [signed_square,← pow_add,heu]; ring
  have hl (a b : ℝ) :
      ((-1:ℝ)^h*z^(h*(r-s)+h.choose 2)*gaussian z s h)*
        ((-1:ℝ)^(h-1)*z^(h.choose 2)*a*b)=
      -(z^(h*(r-s+h-1))*gaussian z s h*a*b) := by
    calc
      _ = ((-1:ℝ)^h*(-1)^(h-1))*(z^(h*(r-s)+h.choose 2)*z^(h.choose 2))*gaussian z s h*a*b := by ring
      _ = _ := by rw [signed_adjacent h hh,← pow_add,hel]; ring
  rw [kernelBlock_coeff_orientations,first_orientation_sum z hz0 hz1 (r-h) h k hk,mul_add]
  by_cases hhk : h≤k
  · rw [ite_eq_left hhk,second_orientation_sum z hz0 hz1 (r-h) h (k-h) hh (by omega)]
    rw [show r-h-(k-h)=r-k by omega]
    simp only [mul_ite,mul_zero,hu,hl,upperPartialTerm,lowerPartialTerm,hhk,true_and]
    by_cases ha : h<k <;> by_cases hb : k≤r-h <;> by_cases hc : h≤r-k <;>
      simp [ha,hb,hc]; ring
  · rw [ite_eq_right hhk,mul_zero,add_zero]
    simp only [mul_ite,mul_zero,hu,upperPartialTerm,lowerPartialTerm,hhk,false_and,ite_false,sub_zero]
    have hhnot : ¬h<k := by omega
    simp [hhnot]

end BoseBurton
