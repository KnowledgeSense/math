import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

noncomputable section
namespace Paving

/-- The cleared inequality for the largest-hyperplane weight. -/
def paymentPolynomial (a s b : ℝ) : ℝ :=
  s*((a+2*b)*(s+b)+(2*b+1)*a*(a+b))*(a+s+2*b+1)-
    (a+s-1)*(a+b)*(s+b)*(a+2*b+(2*b+1)*s)

theorem paymentPolynomial_positive {a s b : ℝ} (hsa : s≤a) (hs : 1≤s) (hb : 1≤b) :
    0<paymentPolynomial a s b := by
  let x := a-s
  have hx : 0≤x := sub_nonneg.mpr hsa
  have hs0 : 0<s := by linarith
  have hb0 : 0<b := by linarith
  have hs2 : 0≤s^2-1 := by nlinarith
  have hs3 : 0≤s^3-1 := by nlinarith [mul_nonneg (show 0≤s-1 by linarith) (show 0≤s^2+s+1 by positivity)]
  have hb2 : 0<4*b^2-2*b+2 := by nlinarith [sq_nonneg (2*b-1)]
  have hb3 : 0<2*b^3-2*b^2+8*b := by
    have h := mul_nonneg (show 0≤b by positivity) (show 0≤b-1 by linarith)
    nlinarith [mul_nonneg (show 0≤b by positivity) h]
  have h0 : 0<2*(s+b)*((b+1)*s+b)*(2*s+b) := by positivity
  have h1 : 0<4*b*(s^3-1)+(6*b^2+2*b+6)*(s^2-1)+
      (2*b^3-2*b^2+8*b)*(s-1)+(7*b^2+14*b+6) := by positivity
  have h2 : 0<6*b*(s^2-1)+(4*b^2-2*b+2)*(s-1)+(b^2+5*b+2) := by positivity
  have h3 : 0<b*(2*s-1) := mul_pos hb0 (by linarith)
  have he : paymentPolynomial a s b=
      2*(s+b)*((b+1)*s+b)*(2*s+b)+
      (4*b*(s^3-1)+(6*b^2+2*b+6)*(s^2-1)+
        (2*b^3-2*b^2+8*b)*(s-1)+(7*b^2+14*b+6))*x+
      (6*b*(s^2-1)+(4*b^2-2*b+2)*(s-1)+(b^2+5*b+2))*x^2+
      b*(2*s-1)*x^3 := by unfold paymentPolynomial; dsimp [x]; ring
  rw [he]
  positivity

/-- The scalar largest-hyperplane bound, including equality of its two size parameters. -/
theorem largest_weight_payment {a s b : ℝ} (hsa : s≤a) (hs : 1≤s) (hb : 1≤b) :
    (a+s-1)/(a+s+2*b+1)<
      s*((a+2*b)/(a+b)+(2*b+1)*a/(s+b))/(a+2*b+(2*b+1)*s) := by
  have ha : 0<a := by linarith
  have hs0 : 0<s := by linarith
  have hb0 : 0<b := by linarith
  have h1 : 0<a+b := by positivity
  have h2 : 0<s+b := by positivity
  have h3 : 0<a+s+2*b+1 := by positivity
  have h4 : 0<a+2*b+(2*b+1)*s := by positivity
  apply (div_lt_div_iff₀ h3 h4).mpr
  have hp := paymentPolynomial_positive hsa hs hb
  apply (mul_lt_mul_iff_left₀ (mul_pos h1 h2)).mp
  field_simp
  unfold paymentPolynomial at hp
  nlinarith [hp]

end Paving
