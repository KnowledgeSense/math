import BoseBurton.TelescopingDefinitions
import BoseBurton.GaussianIdentities

noncomputable section
namespace BoseBurton

theorem cancellationWeight_zero (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (r s : ℕ) :
    cancellationWeight z r s 0=1 := by
  simp [cancellationWeight,gaussian_zero_right z hz0 hz1,
    (qFactorial_pos z hz0 hz1 r).ne',qFactorial_zero]

theorem cancellationWeight_outside (z : ℝ) (r s j : ℕ) (hj : s<j) :
    cancellationWeight z r s j=0 := by
  simp [cancellationWeight,gaussian_outside z s j hj]

theorem cancellationWeight_step_cleared (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s j : ℕ) (hsr : s<r) (hjs : j<s) :
    cancellationWeight z r s (j+1)*(1-z^(j+1))^2*(1-z^(r-j))=
      cancellationWeight z r s j*z^(r-s+2*j)*(1-z^(s-j)) := by
  have hjz := (one_sub_pow_pos z hz0 hz1 (j+1) (by omega)).ne'
  have hpr := (qFactorial_pos z hz0 hz1 r).ne'
  have hpj := (qFactorial_pos z hz0 hz1 j).ne'
  have hG : gaussian z s (j+1)=gaussian z s j*(1-z^(s-j))/(1-z^(j+1)) := by
    apply (eq_div_iff hjz).mpr
    exact gaussian_adjacent z hz0 hz1 s j hjs
  have hF : qFactorial z (r-j)=qFactorial z (r-j-1)*(1-z^(r-j)) := by
    conv_lhs => rw [show r-j=(r-j-1)+1 by omega,qFactorial_succ]
    rw [show r-j-1+1=r-j by omega]
  have hpow : z^((j+1)*(r-s+(j+1)-1))=z^(j*(r-s+j-1))*z^(r-s+2*j) := by
    rw [← pow_add]
    congr 1
    have h1 : r-s+(j+1)-1=r-s+j := by omega
    have h2 : r-s+j-1=(r-s-1)+j := by omega
    rw [h1,h2]
    have hc : r-s=(r-s-1)+1 := by omega
    rw [hc]
    simp only [Nat.add_sub_cancel]
    ring
  unfold cancellationWeight
  rw [hG,hF,hpow,qFactorial_succ,show r-(j+1)=r-j-1 by omega]
  field_simp

theorem positiveWeight_cancellation_cleared (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s j : ℕ) (hsr : s<r) (hjs : j≤s) :
    positiveWeight z r s j*(1-z^(r-j))=
      cancellationWeight z r s j*z^(2*j)*(1-z^(r-s)) := by
  have hpr := (qFactorial_pos z hz0 hz1 r).ne'
  have hpj := (qFactorial_pos z hz0 hz1 j).ne'
  have hF : qFactorial z (r-j)=qFactorial z (r-j-1)*(1-z^(r-j)) := by
    conv_lhs => rw [show r-j=(r-j-1)+1 by omega,qFactorial_succ]
    rw [show r-j-1+1=r-j by omega]
  have hpow : z^(j*(r-s+j+1))=z^(j*(r-s+j-1))*z^(2*j) := by
    rw [← pow_add]
    congr 1
    have h : r-s+j+1=(r-s+j-1)+2 := by omega
    rw [h]; ring
  unfold positiveWeight cancellationWeight
  rw [hF,hpow]
  field_simp

theorem positiveWeight_telescoping (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s j : ℕ) (hsr : s<r) (hjs : j≤s) :
    positiveWeight z r s j=cancellationWeight z r s j*z^(2*j)-
      cancellationWeight z r s (j+1)*(1-z^(j+1))^2 := by
  have hd := (one_sub_pow_pos z hz0 hz1 (r-j) (by omega)).ne'
  have hstep : cancellationWeight z r s (j+1)*(1-z^(j+1))^2*(1-z^(r-j))=
      cancellationWeight z r s j*z^(r-s+2*j)*(1-z^(s-j)) := by
    by_cases hj : j<s
    · exact cancellationWeight_step_cleared z hz0 hz1 r s j hsr hj
    · have he : j=s := by omega
      subst j
      simp [cancellationWeight_outside z r s (s+1) (by omega)]
  have hw := positiveWeight_cancellation_cleared z hz0 hz1 r s j hsr hjs
  have he : z^(r-s)*z^(s-j)=z^(r-j) := by rw [← pow_add]; congr 1; omega
  rw [show z^(r-s+2*j)=z^(r-s)*z^(2*j) by rw [pow_add]] at hstep
  apply (mul_right_inj' hd).mp
  linear_combination hw+hstep-cancellationWeight z r s j*z^(2*j)*he

end BoseBurton
