import AperyMoments.EllipticCut

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem elliptic_integrand_conj {z : ℂ} (hz : z ∈ ellipticDomain) (θ : ℝ) :
    (1 - (starRingEnd ℂ z) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      starRingEnd ℂ ((1 - z * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) := by
  have h := Complex.conj_cpow (1 - z * (Real.sin θ : ℂ) ^ 2) (-(1 / 2 : ℂ))
    (Complex.slitPlane_arg_ne_pi (elliptic_base_mem_slitPlane hz θ))
  have hp : starRingEnd ℂ (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by
    apply Complex.ext <;> norm_num
  rw [hp, map_sub, map_one, map_mul, map_pow, Complex.conj_ofReal] at h
  exact h

theorem complexEllipticK_conj {z : ℂ} (hz : z ∈ ellipticDomain) :
    complexEllipticK (starRingEnd ℂ z) = starRingEnd ℂ (complexEllipticK z) := by
  unfold complexEllipticK
  simp_rw [elliptic_integrand_conj hz]
  exact Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
    ((complexEllipticK_integrand_continuous hz).intervalIntegrable _ _)

/-- The upper-lip value is the conjugate of the lower-lip value. -/
theorem complexEllipticK_upper_cut_limit {m : ℝ} (hm : 1 < m) :
    Tendsto (fun ε : ℝ => complexEllipticK ((m : ℂ) + Complex.I * ε))
      (𝓝[>] 0) (𝓝 (starRingEnd ℂ (complexEllipticK m))) := by
  have ht := Complex.continuous_conj.continuousAt.tendsto.comp (complexEllipticK_lower_cut_limit hm)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hz : (m : ℂ) - Complex.I * ε ∈ ellipticDomain := by
    left
    simpa using ne_of_gt hε
  have he := complexEllipticK_conj hz
  simpa using he.symm

end AperyMoments
