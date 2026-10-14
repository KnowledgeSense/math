import BoseBurton.EndpointExpansion
import BoseBurton.InternalConcavity

noncomputable section
namespace BoseBurton
open Finset

theorem positiveExpansion_two_increment_bound (z : ℝ) (hz0 : 0<z) (hzhalf : z≤1/2)
    (r s : ℕ) (hsr : s<r) (hs : 1≤s) (hr : 3≤r) :
    positiveWeight z r s 1*pairedProduct z r 1 2/positiveWeight z r s 0≤z^(r-s+1) := by
  have hz1 : z<1 := by linarith
  rw [positiveExpansion_two_increment_ratio z hz0 hz1 r s hsr hs hr]
  have hd : 0<1-z := by linarith
  have hR := one_sub_pow_pos z hz0.le hz1 (r-1) (by omega)
  have hpow : z^(r-1)≤z^(r-3) := pow_le_pow_of_le_one hz0.le hz1.le (by omega)
  have hf : (1-z^(r-3))/(1-z^(r-1))≤1 := (div_le_one hR).mpr (by linarith)
  have hS : 0≤1-z^s := (one_sub_pow_pos z hz0.le hz1 s (by omega)).le
  have hS1 : 1-z^s≤1 := by have := pow_nonneg hz0.le s; linarith
  have hprod : (1-z^s)*((1-z^(r-3))/(1-z^(r-1)))≤1 := by
    exact le_trans (mul_le_mul_of_nonneg_left hf hS) (by simpa only [mul_one] using hS1)
  have hm := mul_le_mul_of_nonneg_left hprod (div_nonneg (pow_nonneg hz0.le (r-s+2)) hd.le)
  have hp : z^(r-s+2)/(1-z)≤z^(r-s+1) := by
    apply (div_le_iff₀ hd).mpr
    rw [show r-s+2=(r-s+1)+1 by omega,pow_succ]
    nlinarith [pow_nonneg hz0.le (r-s+1)]
  calc
    _ = (z^(r-s+2)/(1-z))*((1-z^s)*((1-z^(r-3))/(1-z^(r-1)))) := by field_simp
    _ ≤ z^(r-s+2)/(1-z) := by simpa using hm
    _ ≤ z^(r-s+1) := hp

theorem positiveExpansion_endpoint_concave (z : ℝ) (hz0 : 0<z) (hzhalf : z≤1/2)
    (r s : ℕ) (hsr : s<r) (hs : 1≤s) (hr : 3≤r) :
    endpointFactor z r s+
      (∑ j∈range (s+1),positiveWeight z r s j*pairedProduct z r j 2)≤
      2*positiveWeight z r s 0 := by
  have hz1 : z<1 := by linarith
  rw [positiveExpansion_two z r s hs]
  have h1 := positiveExpansion_two_increment_bound z hz0 hzhalf r s hsr hs hr
  have h2 := endpointFactor_reserve z hz0 hz1 r s hsr hs
  have hw := positiveWeight_pos z hz0 hz1 r s 0 hsr (by omega)
  have h := (div_le_iff₀ hw).mp
    (show (endpointFactor z r s+positiveWeight z r s 1*pairedProduct z r 1 2)/
      positiveWeight z r s 0≤1 by rw [add_div]; linarith)
  linarith

end BoseBurton
