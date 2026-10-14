import HardCoreActivityThreshold.FivefoldMinimum

namespace HardCoreActivityThreshold

theorem thirdPartitionDerivative_strictMonoOn :
    StrictMonoOn thirdPartitionDerivative (Set.Ioc 0 concavityEndpoint) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 concavityEndpoint)
  · intro x hx
    exact (thirdPartitionDerivative_hasDerivAt x hx.1).continuousAt.continuousWithinAt
  · intro x hx
    have hi := interior_subset hx
    rw [(thirdPartitionDerivative_hasDerivAt x hi.1).deriv]
    exact fourthPartitionDerivative_pos x hi.1 hi.2

theorem secondPartitionDerivative_strictConvexOn :
    StrictConvexOn ℝ (Set.Ioc 0 concavityEndpoint) secondPartitionDerivative := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioc 0 concavityEndpoint)
  · intro x hx
    exact (secondPartitionDerivative_hasDerivAt x hx.1).continuousAt.continuousWithinAt
  · intro x hx y hy hxy
    have hix := interior_subset hx
    have hiy := interior_subset hy
    rw [(secondPartitionDerivative_hasDerivAt x hix.1).deriv,
      (secondPartitionDerivative_hasDerivAt y hiy.1).deriv]
    exact thirdPartitionDerivative_strictMonoOn hix hiy hxy

end HardCoreActivityThreshold
