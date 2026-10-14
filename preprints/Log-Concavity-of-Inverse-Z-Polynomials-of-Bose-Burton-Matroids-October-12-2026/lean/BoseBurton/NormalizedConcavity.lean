import BoseBurton.EndpointConcavity
import BoseBurton.GaussianConcavity

noncomputable section
namespace BoseBurton
open Finset

theorem normalizedCoefficient_one (z : ℝ) (r s : ℕ) (hr : 2≤r) :
    normalizedCoefficient z r s 1=positiveWeight z r s 0 := by
  rw [normalizedCoefficient,ite_eq_right (by omega),positiveExpansion_one]

theorem normalizedCoefficient_lower_concave (z : ℝ) (hz0 : 0<z) (hzhalf : z≤1/2)
    (r s k : ℕ) (hsr : s<r) (hs : 1≤s) (hk : 1≤k) (hkr : 2*k≤r) :
    normalizedCoefficient z r s (k-1)+normalizedCoefficient z r s (k+1)≤
      2*normalizedCoefficient z r s k := by
  have hz1 : z<1 := by linarith
  by_cases hk1 : k=1
  · subst k
    rw [normalizedCoefficient_one z r s (by omega)]
    by_cases hr2 : r=2
    · subst r
      simp only [Nat.reduceSub,Nat.reduceAdd,normalizedCoefficient,eq_self,or_true,
        true_or,ite_true]
      have h := endpointFactor_reserve z hz0 hz1 2 s hsr hs
      have hw := positiveWeight_pos z hz0 hz1 2 s 0 hsr (by omega)
      have he : endpointFactor z 2 s≤positiveWeight z 2 s 0 := by
        apply (div_le_one hw).mp
        have := pow_nonneg hz0.le (2-s+1)
        linarith
      linarith
    · simpa only [Nat.reduceSub,Nat.reduceAdd,normalizedCoefficient,
        show ¬(2=0 ∨ 2=r) by omega,ite_false,eq_self,true_or,ite_true] using
        positiveExpansion_endpoint_concave z hz0 hzhalf r s hsr hs (by omega)
  · simp only [normalizedCoefficient,
      show ¬(k-1=0 ∨ k-1=r) by omega,show ¬(k+1=0 ∨ k+1=r) by omega,
      show ¬(k=0 ∨ k=r) by omega,ite_false]
    exact positiveExpansion_internal_concave z hz0 hzhalf r s k hsr (by omega) hkr

theorem normalizedCoefficient_concave (z : ℝ) (hz0 : 0<z) (hzhalf : z≤1/2)
    (r s k : ℕ) (hsr : s<r) (hs : 1≤s) (hk : 1≤k) (hkr : k<r) :
    normalizedCoefficient z r s (k-1)+normalizedCoefficient z r s (k+1)≤
      2*normalizedCoefficient z r s k := by
  by_cases hhalf : 2*k≤r
  · exact normalizedCoefficient_lower_concave z hz0 hzhalf r s k hsr hs hk hhalf
  · have h := normalizedCoefficient_lower_concave z hz0 hzhalf r s (r-k) hsr hs
      (by omega) (by omega)
    rw [show r-k-1=r-(k+1) by omega,show r-k+1=r-(k-1) by omega,
      normalizedCoefficient_symm z r s (k+1) (by omega),
      normalizedCoefficient_symm z r s (k-1) (by omega),
      normalizedCoefficient_symm z r s k (by omega)] at h
    linarith

theorem scalarCoefficient_strict_log_concave (z : ℝ) (hz0 : 0<z) (hzhalf : z≤1/2)
    (r s k : ℕ) (hsr : s<r) (hs : 1≤s) (hk : 1≤k) (hkr : k<r) :
    scalarCoefficient z r s (k-1)*scalarCoefficient z r s (k+1)<
      scalarCoefficient z r s k^2 := by
  have hz1 : z<1 := by linarith
  exact gaussian_times_concave_strict z hz0 hz1 r k hk hkr
    (normalizedCoefficient z r s (k-1)) (normalizedCoefficient z r s k)
    (normalizedCoefficient z r s (k+1))
    (normalizedCoefficient_pos z hz0 hz1 r s (k-1) hsr)
    (normalizedCoefficient_pos z hz0 hz1 r s k hsr)
    (normalizedCoefficient_pos z hz0 hz1 r s (k+1) hsr)
    (normalizedCoefficient_concave z hz0 hzhalf r s k hsr hs hk hkr)

end BoseBurton
