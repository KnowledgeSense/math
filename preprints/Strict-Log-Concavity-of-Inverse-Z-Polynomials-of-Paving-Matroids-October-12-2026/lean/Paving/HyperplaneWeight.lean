import Paving.ScalarPayment
import Mathlib.Data.Nat.Choose.Basic

noncomputable section
namespace Paving

theorem choose_add_linear_lower (h s r : ℕ) :
    h.choose (r+1)+s*h.choose r ≤ (h+s).choose (r+1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hc := Nat.choose_le_add h s r
    rw [show h+(s+1)=(h+s)+1 by omega,Nat.choose_succ_succ]
    nlinarith

theorem choose_weight_bound {h s r : ℕ} (hr : 1 ≤ r) (_hrh : r ≤ h) :
    (h+r*s)*h.choose r ≤ h*(h+s).choose r := by
  have he : r-1+1=r := by omega
  have hl := choose_add_linear_lower h s (r-1)
  rw [he] at hl
  have hc := Nat.choose_succ_right_eq h (r-1)
  rw [he] at hc
  have hsmall : h-(r-1) ≤ h := Nat.sub_le _ _
  have hcross : r*h.choose r ≤ h*h.choose (r-1) := by nlinarith
  nlinarith [Nat.mul_le_mul_left h hl,Nat.mul_le_mul_left s hcross]

theorem choose_weight_ratio_bound {h s r : ℕ} (hr : 1 ≤ r) (hrh : r ≤ h) :
    (h.choose r:ℝ)/((h+s).choose r:ℝ) ≤ (h:ℝ)/((h:ℝ)+r*s) := by
  have hh : 0 < (h:ℝ) := by exact_mod_cast (show 0 < h by omega)
  have hd : 0 < ((h+s).choose r:ℝ) := by
    exact_mod_cast Nat.choose_pos (show r ≤ h+s by omega)
  have hd2 : 0 < (h:ℝ)+r*s := by positivity
  apply (div_le_div_iff₀ hd hd2).mpr
  rw [mul_comm (h.choose r:ℝ)]
  exact_mod_cast choose_weight_bound (s:=s) hr hrh

/-- Coupled payment after reserving the unique largest hyperplane. -/
theorem large_hyperplane_mixture_lower {a s b α x : ℝ}
    (hsa : s ≤ a) (hs : 1 ≤ s) (hb : 1 ≤ b)
    (hα : α ≤ (a+2*b)/(a+2*b+(2*b+1)*s))
    (hx : α*(s/(a+b))+(1-α)*(a/(s+b)) ≤ x) :
    (a+s-1)/(a+s+2*b+1) < x := by
  have ha : 0 < a := by linarith
  have hs0 : 0 < s := by linarith
  have hb0 : 0 < b := by linarith
  have hab : 0 < a+b := by positivity
  have hsb : 0 < s+b := by positivity
  have hd : 0 < a+2*b+(2*b+1)*s := by positivity
  have hv : s/(a+b) ≤ a/(s+b) := by
    apply (div_le_div_iff₀ hab hsb).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hsa) (show 0 ≤ a+s+b by positivity)]
  have hm := mul_le_mul_of_nonpos_right hα (show s/(a+b)-a/(s+b) ≤ 0 by linarith)
  have he : (a+2*b)/(a+2*b+(2*b+1)*s)*(s/(a+b))+
      (1-(a+2*b)/(a+2*b+(2*b+1)*s))*(a/(s+b))=
      s*((a+2*b)/(a+b)+(2*b+1)*a/(s+b))/(a+2*b+(2*b+1)*s) := by
    field_simp
    ring
  have hp := largest_weight_payment hsa hs hb
  rw [← he] at hp
  linarith

end Paving
