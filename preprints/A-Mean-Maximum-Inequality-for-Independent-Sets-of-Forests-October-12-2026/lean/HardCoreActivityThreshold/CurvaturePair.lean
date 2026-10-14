import HardCoreActivityThreshold.CurvatureConvexity
import HardCoreActivityThreshold.StrictTrapezoid

namespace HardCoreActivityThreshold

open Set intervalIntegral

theorem curvature_pair_positive (u v : ℝ) (hu : 0<u) (huv : u<v)
    (hv : v≤concavityEndpoint) (he : firstPartitionDerivative u=firstPartitionDerivative v) :
    0<secondPartitionDerivative u+secondPartitionDerivative v := by
  have hsub : Icc u v⊆Ioc 0 concavityEndpoint := by
    intro t ht
    exact ⟨hu.trans_le ht.1,ht.2.trans hv⟩
  have hconv := secondPartitionDerivative_strictConvexOn.subset hsub (convex_Icc u v)
  have hc : ContinuousOn secondPartitionDerivative (Icc u v) := by
    intro t ht
    exact (secondPartitionDerivative_hasDerivAt t (hsub ht).1).continuousAt.continuousWithinAt
  have hint : (∫t in u..v,secondPartitionDerivative t)=0 := by
    have hd : ∀t∈uIcc u v,HasDerivAt firstPartitionDerivative (secondPartitionDerivative t) t := by
      intro t ht
      rw [uIcc_of_le huv.le] at ht
      exact firstPartitionDerivative_hasDerivAt t (hsub ht).1
    rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc huv.le),←he,sub_self]
  have h := strict_trapezoid huv hconv hc
  rw [hint] at h
  have hp : 0<v-u := sub_pos.mpr huv
  nlinarith

end HardCoreActivityThreshold
