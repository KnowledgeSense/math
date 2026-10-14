import Dowling.DowlingWeightedMixtureFunctions

noncomputable section
namespace Dowling
open Finset

/-- The whole supported mixture is strictly log-concave at every internal index. -/
theorem weightedMixtureCoefficient_strict_log_concave {W : ℕ→ℝ} {p : ℝ} (n k : ℕ)
    (hW : ∀ j,2*j≤n→0<W j)
    (hmid : ∀ i j,2*i≤n→2*j≤n→W i*W j≤W ((i+j)/2)*W ((i+j+1)/2)) (hp : 1<p) (hk : 1≤k) (hkn : k<n) :
    weightedMixtureCoefficient W p n (k-1)*weightedMixtureCoefficient W p n (k+1)<
      (weightedMixtureCoefficient W p n k)^2 := by
  have h := discrete_midpoint_strict
    (weightedMixtureFunction W p n (k-1)) (weightedMixtureFunction W p n (k+1))
    (weightedMixtureFunction W p n k) n
    (weightedMixtureFunction_nonneg n (k-1) hW hp)
    (weightedMixtureFunction_nonneg n (k+1) hW hp)
    (weightedMixtureFunction_nonneg n k hW hp)
    (weightedMixtureFunction_support W p n (k-1))
    (weightedMixtureFunction_support W p n (k+1))
    (weightedMixtureFunction_support W p n k)
    (weightedMixtureFunction_midpoint_strict n k hW hmid hp hk hkn)
    (mul_pos (weightedMixtureFunction_sum_pos n (k-1) hW hp (by omega))
      (weightedMixtureFunction_sum_pos n (k+1) hW hp (by omega)))
  simpa only [weightedMixtureFunction_sum] using h

theorem weightedMixtureCoefficient_strict_of_log_concave {W : ℕ→ℝ} {p : ℝ} (n k : ℕ)
    (hW : ∀ j,2*j≤n→0<W j)
    (hlc : ∀ j,1≤j→2*(j+1)≤n→W (j-1)*W (j+1)≤W j^2)
    (hp : 1<p) (hk : 1≤k) (hkn : k<n) :
    weightedMixtureCoefficient W p n (k-1)*weightedMixtureCoefficient W p n (k+1)<
      (weightedMixtureCoefficient W p n k)^2 := by
  apply weightedMixtureCoefficient_strict_log_concave n k hW
  · intro i j hi hj
    exact finite_weight_midpoint W (n/2) (fun q hq=>hW q (by omega))
      (fun q hq hqJ=>hlc q hq (by omega)) i j (by omega) (by omega)
  · exact hp
  · exact hk
  · exact hkn

end Dowling
