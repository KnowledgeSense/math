import BoseBurton.GaussianDuality
import BoseBurton.SignedKernel

noncomputable section
namespace BoseBurton

theorem choose_two_add (a b : ℕ) : (a+b).choose 2=a.choose 2+b.choose 2+a*b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h1 : (a+(b+1)).choose 2=(a+b).choose 2+(a+b) := by
      rw [show a+(b+1)=(a+b)+1 by omega,Nat.choose_succ_succ]; simp; omega
    have h2 : (b+1).choose 2=b.choose 2+b := by rw [Nat.choose_succ_succ]; simp; omega
    rw [h1,h2,ih]
    ring

theorem kernel_exponent_balance (r s h l : ℕ) (hsr : s≤r) (hhs : h≤s) (hhl : h+l≤r) :
    (h*(s-h)+l*(r-h-l)+(r-h-l).choose 2)+
      (h*(r-s)+h.choose 2+l.choose 2)=r.choose 2 := by
  have he : r=h+(l+(r-h-l)) := by omega
  have hc := congrArg (fun n=>n.choose 2) he
  rw [choose_two_add,choose_two_add] at hc
  have hm : h*(s-h)+h*(r-s)=h*(r-h) := by
    rw [← mul_add]
    congr 1
    omega
  have hr : r-h=l+(r-h-l) := by omega
  rw [hr] at hm
  nlinarith

theorem kernel_scalar_dual (q : ℝ) (hq : 1<q) (r s h l : ℕ)
    (hsr : s≤r) (hhs : h≤s) (hhl : h+l≤r) :
    gaussian q s h*gaussian q (r-h) l*q^((r-h-l).choose 2)=
      q^(r.choose 2)*(q⁻¹)^(h*(r-s)+h.choose 2+l.choose 2)*
        gaussian q⁻¹ s h*gaussian q⁻¹ (r-h) l := by
  have hq0 : q≠0 := by linarith
  rw [gaussian_dual q hq s h hhs,gaussian_dual q hq (r-h) l (by omega)]
  have he := kernel_exponent_balance r s h l hsr hhs hhl
  have hp : q^(h*(s-h)+l*(r-h-l)+(r-h-l).choose 2)=
      q^(r.choose 2)*(q⁻¹)^(h*(r-s)+h.choose 2+l.choose 2) := by
    rw [← he,pow_add,inv_pow]
    field_simp
    simp only [pow_add]
  have heq : q^(h*(s-h))*q^(l*(r-h-l))*q^((r-h-l).choose 2)=
      q^(r.choose 2)*(q⁻¹)^(h*(r-s)+h.choose 2+l.choose 2) := by
    rw [← pow_add,← pow_add]
    exact hp
  linear_combination gaussian q⁻¹ s h*gaussian q⁻¹ (r-h) l*heq

end BoseBurton
