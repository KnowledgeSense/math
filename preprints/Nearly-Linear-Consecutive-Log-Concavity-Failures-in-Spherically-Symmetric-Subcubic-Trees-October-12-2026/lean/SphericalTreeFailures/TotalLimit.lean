import SphericalTreeFailures.TailLimit
import SphericalTreeFailures.TotalDecomposition
import SphericalTreeFailures.CumulativeCensus

set_option maxHeartbeats 1000000

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable def coreLift (p : unitInterval) (k : ℕ) (activity : ℝ) (ha : 0 < activity) :
    Lp ℝ 2 (broadcastMeasure p) →ₗᵢ[ℝ] Lp ℝ 2 (totalSizeMeasure p k activity ha) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst

noncomputable def totalFluctuationL2 (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) : Lp ℝ 2 (totalSizeMeasure p k activity ha) :=
  coreLift p k activity ha (cumulativeCensusL2 p i m) +
    tailMeanDifference k activity • coreLift p k activity ha (censusL2 p i m) +
    normalizedTailL2 p k m activity ha i (censusScale p)

noncomputable def totalLimitL2 (p : unitInterval) (k : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) : Lp ℝ 2 (totalSizeMeasure p k activity ha) :=
  (tailMeanDifference k activity + censusScale p / (1 + censusScale p)) •
    coreLift p k activity ha (censusLimitL2 p i)

theorem totalFluctuationL2_tendsto (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (k : ℕ) (activity : ℝ) (ha : 0 < activity) (i : Bool) :
    Tendsto (fun m => totalFluctuationL2 p k m activity ha i) atTop
      (𝓝 (totalLimitL2 p k activity ha i)) := by
  have h1 := (coreLift p k activity ha).continuous.tendsto
    ((censusScale p / (1 + censusScale p)) • censusLimitL2 p i) |>.comp
      (cumulativeCensusL2_tendsto p hc i)
  have h2 := ((coreLift p k activity ha).continuous.tendsto (censusLimitL2 p i) |>.comp
    (censusL2_tendsto p hc i)).const_smul (tailMeanDifference k activity)
  have h3 := normalizedTailL2_tendsto p k activity ha i (censusScale p)
    (by unfold censusScale; nlinarith : 2 < censusScale p ^ 2)
  have h := (h1.add h2).add h3
  have he : coreLift p k activity ha ((censusScale p / (1 + censusScale p)) • censusLimitL2 p i) +
      tailMeanDifference k activity • coreLift p k activity ha (censusLimitL2 p i) + 0 =
        totalLimitL2 p k activity ha i := by
    rw [map_smul, add_zero, ← add_smul]
    unfold totalLimitL2
    rw [add_comm (censusScale p / (1 + censusScale p)) (tailMeanDifference k activity)]
  rw [he] at h
  exact h

theorem coreLift_ae_eq (p : unitInterval) (k : ℕ) (activity : ℝ) (ha : 0 < activity)
    (f : Lp ℝ 2 (broadcastMeasure p)) :
    (coreLift p k activity ha f : TotalSizeSpace k → ℝ) =ᵐ[totalSizeMeasure p k activity ha]
      fun ω => f ω.1 := Lp.coeFn_compMeasurePreserving _ _

theorem totalFluctuationL2_ae_eq (p : unitInterval) (hp : 0 < (p : ℝ))
    (k m : ℕ) (activity : ℝ) (ha : 0 < activity) (i : Bool) :
    (totalFluctuationL2 p k m activity ha i : TotalSizeSpace k → ℝ) =ᵐ[totalSizeMeasure p k activity ha]
      fun ω => ((-censusScale p) ^ m)⁻¹ *
        (sampledTotalSize k m i ω - totalCenter p k m activity) := by
  have hc := (measurePreserving_fst (μ := broadcastMeasure p)
    (ν := tailInputMeasure k activity ha)).quasiMeasurePreserving.ae
      (cumulativeCensusL2_ae_eq p hp i m)
  have hm := (measurePreserving_fst (μ := broadcastMeasure p)
    (ν := tailInputMeasure k activity ha)).quasiMeasurePreserving.ae
      (memLp_censusMartingale p i m 2).coeFn_toLp
  have hn := ((memLp_tailNoise p k m activity ha i 2).const_mul
    (((-censusScale p) ^ m)⁻¹)).coeFn_toLp
  filter_upwards [hc, hm, hn, coreLift_ae_eq p k activity ha (cumulativeCensusL2 p i m),
    coreLift_ae_eq p k activity ha (censusL2 p i m),
    Lp.coeFn_smul (tailMeanDifference k activity) (coreLift p k activity ha (censusL2 p i m)),
    Lp.coeFn_add (coreLift p k activity ha (cumulativeCensusL2 p i m))
      (tailMeanDifference k activity • coreLift p k activity ha (censusL2 p i m)),
    Lp.coeFn_add (coreLift p k activity ha (cumulativeCensusL2 p i m) +
      tailMeanDifference k activity • coreLift p k activity ha (censusL2 p i m))
      (normalizedTailL2 p k m activity ha i (censusScale p))]
    with ω hC hM hN hLc hLm hS hA hB
  change (normalizedTailL2 p k m activity ha i (censusScale p)) ω = _ at hN
  change (censusL2 p i m) ω.1 = _ at hM
  change _ = cumulativeCensus p i m ω.1 at hC
  change _ = _ at hB
  unfold totalFluctuationL2
  rw [hB, Pi.add_apply, hA, Pi.add_apply, hS, Pi.smul_apply, smul_eq_mul,
    hLc, hLm, hC, hM, hN, sampledTotalSize_decomposition]
  unfold cumulativeCensus censusMartingale
  ring

theorem totalLimitL2_ae_eq (p : unitInterval) (k : ℕ) (activity : ℝ) (ha : 0 < activity)
    (i : Bool) :
    (totalLimitL2 p k activity ha i : TotalSizeSpace k → ℝ) =ᵐ[totalSizeMeasure p k activity ha]
      fun ω => (tailMeanDifference k activity + censusScale p / (1 + censusScale p)) *
        censusLimit p i ω.1 := by
  filter_upwards [Lp.coeFn_smul
    (tailMeanDifference k activity + censusScale p / (1 + censusScale p))
    (coreLift p k activity ha (censusLimitL2 p i)),
    coreLift_ae_eq p k activity ha (censusLimitL2 p i)] with ω hs hl
  rw [totalLimitL2, hs, Pi.smul_apply, smul_eq_mul, hl]
  rfl

theorem sampledTotalSize_tendsto_L2 (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (k : ℕ) (activity : ℝ) (ha : 0 < activity) (i : Bool) :
    Tendsto (fun m => eLpNorm (fun ω : TotalSizeSpace k =>
      ((-censusScale p) ^ m)⁻¹ * (sampledTotalSize k m i ω - totalCenter p k m activity) -
        (tailMeanDifference k activity + censusScale p / (1 + censusScale p)) *
          censusLimit p i ω.1) 2 (totalSizeMeasure p k activity ha)) atTop (𝓝 0) := by
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  have ht := (totalFluctuationL2_tendsto p hc k activity ha i).edist
    (tendsto_const_nhds (x := totalLimitL2 p k activity ha i))
  simp only [edist_self] at ht
  apply ht.congr'
  exact Eventually.of_forall fun m => by
    dsimp only
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((totalFluctuationL2_ae_eq p hp k m activity ha i).sub
      (totalLimitL2_ae_eq p k activity ha i))

theorem totalCenterDensity_tuned (k : ℕ) (r : ℝ) :
    totalCenterDensity (broadcastParameter r) k (tunedActivity r) = asymptoticDensity k r := by
  unfold totalCenterDensity tailMeanDifference asymptoticDensity stationaryProbability stationaryDensity
  ring

theorem totalLimitFactor_tuned (k : ℕ) (r : ℝ) :
    tailMeanDifference k (tunedActivity r) +
      censusScale (broadcastParameter r) / (1 + censusScale (broadcastParameter r)) = tailShift k r := rfl

end SphericalTreeFailures
