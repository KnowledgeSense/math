import SphericalTreeFailures.CensusVariance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # The genuine L² census limit

A summable geometric bound on successive L² distances makes the concrete
normalized census a Cauchy sequence in the complete space `Lp ℝ 2`.
-/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal ProbabilityTheory Topology

/-- The concrete normalized census, as an element of the Hilbert space L². -/
noncomputable def censusL2 (p : unitInterval) (i : Bool) (h : ℕ) :
    Lp ℝ 2 (broadcastMeasure p) :=
  (memLp_censusMartingale p i h 2).toLp (censusMartingale p i h)

theorem norm_toLp_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  simp [hω, Real.norm_eq_abs, sq_abs]

theorem censusL2_increment_sq (p : unitInterval) (i : Bool) (h : ℕ) :
    ‖censusL2 p i (h + 1) - censusL2 p i h‖ ^ 2 =
      ∫ ω, (censusMartingale p i (h + 1) ω - censusMartingale p i h ω) ^ 2
        ∂broadcastMeasure p := by
  exact norm_toLp_sq _ _
    ((memLp_censusMartingale p i (h + 1) 2).sub (memLp_censusMartingale p i h 2))

theorem censusL2_increment_bound (p : unitInterval) (hp : 0 < (p : ℝ)) (i : Bool) (h : ℕ) :
    ‖censusL2 p i (h + 1) - censusL2 p i h‖ ≤
      Real.sqrt ((2 * (p : ℝ) ^ 2)⁻¹) ^ (h + 1) := by
  have hq : 0 ≤ (2 * (p : ℝ) ^ 2)⁻¹ := by positivity
  have hsqrt : Real.sqrt ((2 * (p : ℝ) ^ 2)⁻¹) ^ 2 = (2 * (p : ℝ) ^ 2)⁻¹ :=
    Real.sq_sqrt hq
  have hs : (Real.sqrt ((2 * (p : ℝ) ^ 2)⁻¹) ^ (h + 1)) ^ 2 =
      ((2 * (p : ℝ) ^ 2)⁻¹) ^ (h + 1) := by
    rw [← pow_mul, Nat.mul_comm (h + 1) 2, pow_mul, hsqrt]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hs, censusL2_increment_sq, inv_pow]
  refine (integral_census_increment_sq_bound p hp i h).trans ?_
  have hpe : (p : ℝ) * (1 - p) ≤ 1 := by
    nlinarith [p.property.1, p.property.2, sq_nonneg (p : ℝ)]
  exact mul_le_of_le_one_left (by positivity) hpe

theorem censusL2_cauchy (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    CauchySeq (censusL2 p i) := by
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  have hr0 : 0 ≤ Real.sqrt ((2 * (p : ℝ) ^ 2)⁻¹) := Real.sqrt_nonneg _
  have hr1 : Real.sqrt ((2 * (p : ℝ) ^ 2)⁻¹) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
    simpa using (inv_lt_one₀ (by positivity : 0 < 2 * (p : ℝ) ^ 2)).mpr hc
  apply cauchySeq_of_summable_dist
  have hs : Summable (fun h : ℕ => Real.sqrt ((2 * (p : ℝ) ^ 2)⁻¹) ^ (h + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
  apply hs.of_nonneg_of_le (fun _ => dist_nonneg)
  intro h
  rw [dist_comm, dist_eq_norm]
  exact censusL2_increment_bound p hp i h

theorem exists_censusL2_limit (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    ∃ W : Lp ℝ 2 (broadcastMeasure p), Tendsto (censusL2 p i) atTop (𝓝 W) :=
  cauchySeq_tendsto_of_complete (censusL2_cauchy p hc i)

/-- The L² limit; outside the supercritical region this definition is set to zero. -/
noncomputable def censusLimitL2 (p : unitInterval) (i : Bool) : Lp ℝ 2 (broadcastMeasure p) :=
  if hc : 1 < 2 * (p : ℝ) ^ 2 then Classical.choose (exists_censusL2_limit p hc i) else 0

noncomputable def censusLimit (p : unitInterval) (i : Bool) : BroadcastSpace → ℝ :=
  censusLimitL2 p i

theorem censusL2_tendsto (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    Tendsto (censusL2 p i) atTop (𝓝 (censusLimitL2 p i)) := by
  simpa [censusLimitL2, hc] using Classical.choose_spec (exists_censusL2_limit p hc i)

theorem memLp_censusLimit (p : unitInterval) (i : Bool) :
    MemLp (censusLimit p i) 2 (broadcastMeasure p) := Lp.memLp _

theorem census_tendsto_L2 (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    Tendsto (fun h => eLpNorm (censusMartingale p i h - censusLimit p i) 2 (broadcastMeasure p))
      atTop (𝓝 0) := by
  have ht := (censusL2_tendsto p hc i).edist (tendsto_const_nhds (x := censusLimitL2 p i))
  simp only [edist_self] at ht
  apply ht.congr'
  exact Eventually.of_forall fun h => by
    dsimp only
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((memLp_censusMartingale p i h 2).coeFn_toLp.sub EventuallyEq.rfl)

/-- The conditional limit distribution at a prescribed root state. -/
noncomputable def censusLimitLaw (p : unitInterval) (i : Bool) : Measure ℝ :=
  (broadcastMeasure p).map (censusLimit p i)

instance (p : unitInterval) (i : Bool) : IsProbabilityMeasure (censusLimitLaw p i) :=
  (Measure.isProbabilityMeasure_map_iff (memLp_censusLimit p i).aemeasurable).mpr inferInstance

end SphericalTreeFailures
