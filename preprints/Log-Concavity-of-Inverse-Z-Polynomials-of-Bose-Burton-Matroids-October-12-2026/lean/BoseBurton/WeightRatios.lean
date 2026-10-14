import BoseBurton.PositiveWeights
import BoseBurton.GaussianIdentities

noncomputable section
namespace BoseBurton

theorem positiveWeight_step_cleared (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s j : ℕ) (hsr : s<r) (hjs : j<s) :
    positiveWeight z r s (j+1)*(1-z^(j+1))^2*(1-z^(r-j-1))=
      positiveWeight z r s j*z^(r-s+2*j+2)*(1-z^(s-j)) := by
  have hjz := (one_sub_pow_pos z hz0 hz1 (j+1) (by omega)).ne'
  have hpr := (qFactorial_pos z hz0 hz1 r).ne'
  have hpj := (qFactorial_pos z hz0 hz1 j).ne'
  have hG : gaussian z s (j+1)=gaussian z s j*(1-z^(s-j))/(1-z^(j+1)) := by
    apply (eq_div_iff hjz).mpr
    exact gaussian_adjacent z hz0 hz1 s j hjs
  have hF : qFactorial z (r-j-1)=qFactorial z (r-j-2)*(1-z^(r-j-1)) := by
    conv_lhs => rw [show r-j-1=(r-j-2)+1 by omega,qFactorial_succ]
    rw [show r-j-2+1=r-j-1 by omega]
  have hpow : z^((j+1)*(r-s+(j+1)+1))=z^(j*(r-s+j+1))*z^(r-s+2*j+2) := by
    rw [← pow_add]
    congr 1
    ring
  unfold positiveWeight
  rw [hG,hF,hpow,qFactorial_succ,show r-(j+1)-1=r-j-2 by omega]
  field_simp

theorem positiveWeight_step_ratio (z : ℝ) (hz0 : 0<z) (hz1 : z<1)
    (r s j : ℕ) (hsr : s<r) (hjs : j<s) :
    positiveWeight z r s (j+1)/positiveWeight z r s j=
      z^(r-s+2*j+2)*(1-z^(s-j))/((1-z^(j+1))^2*(1-z^(r-j-1))) := by
  have hw := (positiveWeight_pos z hz0 hz1 r s j hsr (by omega)).ne'
  have hj := (one_sub_pow_pos z hz0.le hz1 (j+1) (by omega)).ne'
  have hr := (one_sub_pow_pos z hz0.le hz1 (r-j-1) (by omega)).ne'
  apply (div_eq_div_iff hw (mul_ne_zero (pow_ne_zero _ hj) hr)).mpr
  have h := positiveWeight_step_cleared z hz0.le hz1 r s j hsr hjs
  nlinarith [h]

end BoseBurton
