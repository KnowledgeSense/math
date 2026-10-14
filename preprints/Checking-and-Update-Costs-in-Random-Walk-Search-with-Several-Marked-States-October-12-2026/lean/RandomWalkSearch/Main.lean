import RandomWalkSearch.ConsecutiveMain
import RandomWalkSearch.ConsecutiveCoordinate
import RandomWalkSearch.RestorationDichotomy
import RandomWalkSearch.Endpoints
import RandomWalkSearch.MarkedMass
import RandomWalkSearch.HittingConsequences
import RandomWalkSearch.Observability

/-! # Main theorems for the fixed lazy-cycle search problem

All universal statements below accept arbitrary measurable, privately randomized
history policies on arbitrary probability spaces. Endpoint witnesses use an
explicit product probability space with independent uniform setup and iid lazy
increments. Counts and expectations are those of actual operational executions.
-/

namespace RandomWalkSearch.Cycle
open MeasureTheory
open scoped ENNReal

variable {k : ℕ} [NeZero (N k)] {Ω : Type*} [MeasurableSpace Ω]

/-- Free restoration, including the explicit dichotomy and both unconditional
coordinate lower bounds from the endpoint theorem. -/
theorem free_restoration_main (A : Randomized k Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hm : A.MeasurableCoordinates)
    (b : ℕ) (hb : 1≤b) (hk : 16*(b+1)≤k) (hA : A.Restoration b)
    (hs : ∀a, (1:ℝ≥0∞)/2 ≤ A.success μ a) :
    (1:ℝ≥0∞)/64 ≤ A.averageChecks μ/L k + A.averageUpdates μ/N k ∧
    ((L k:ℝ≥0∞)/128 ≤ A.averageChecks μ ∨ (N k:ℝ≥0∞)/128 ≤ A.averageUpdates μ) ∧
    (k:ℝ≥0∞)/32 ≤ A.averageChecks μ ∧ (L k:ℝ≥0∞)/64 ≤ A.averageUpdates μ := by
  have ho := hm.observable
  exact ⟨A.restoration_lower_bound μ ho b hb hk hA hs,
    A.restoration_dichotomy μ ho b hb hk hA hs,
    A.checks_lower_bound μ ho.success ho.checks (by omega) hs,
    A.updates_lower_bound μ ho.success ho.updates b hb hk hA hs⟩

/-- Consecutive trajectories, including the unconditional quadratic update
lower bound from the endpoint theorem. -/
theorem consecutive_main (A : Randomized k Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hm : A.MeasurableCoordinates) (hlaw : A.LazyLaw μ)
    (b : ℕ) (hb : 1≤b) (hk : 16*(b+1)≤k) (hA : A.Consecutive b)
    (hs : ∀a, (1:ℝ≥0∞)/2 ≤ A.success μ a) :
    (1:ℝ≥0∞)/(64*b) ≤ A.averageChecks μ/L k + A.averageUpdates μ^(1/(2:ℝ))/N k ∧
      (L k:ℝ≥0∞)^2/(8192*(b:ℝ≥0∞)^2) ≤ A.averageUpdates μ := by
  have ho := hm.observable
  exact ⟨A.consecutive_lower_bound μ ho hlaw b hb hk hA hs,
    A.consecutive_updates_lower_bound μ ho.success ho.updates hlaw b hb hk hA hs⟩

/-- Four endpoint witnesses, including a proved measurable private-randomness
implementation on the concrete independent setup/tape probability space. -/
theorem endpoints_main [NeZero (L k)] (hk : 2≤k) :
    ∃ pRS pRD pCS pCD : Policy (Vertex k),
      IsRestorationEndpoint pRS (4*((L k-1:ℕ):ℝ)) (L k) ∧
      IsRestorationEndpoint pRD (4*((N k-1:ℕ):ℝ)) k ∧
      IsConsecutiveEndpoint pCS (2*(L k:ℝ)^2) (L k) ∧
      IsConsecutiveEndpoint pCD (2*(N k:ℝ)^2) k ∧
      (Canonical.algorithm k pRS).MeasurableCoordinates ∧
      (Canonical.algorithm k pRD).MeasurableCoordinates ∧
      (Canonical.algorithm k pCS).MeasurableCoordinates ∧
      (Canonical.algorithm k pCD).MeasurableCoordinates := by
  obtain ⟨pRS,pRD,pCS,pCD,hRS,hRD,hCS,hCD⟩ := four_endpoints hk
  exact ⟨pRS,pRD,pCS,pCD,hRS,hRD,hCS,hCD,
    Canonical.algorithm_measurableCoordinates pRS,
    Canonical.algorithm_measurableCoordinates pRD,
    Canonical.algorithm_measurableCoordinates pCS,
    Canonical.algorithm_measurableCoordinates pCD⟩

/-- The no-uniform-split corollary with genuine hitting-time and marked-mass
quantities and the exact threshold in the source. -/
theorem no_uniform_split_main [NeZero (L k)] (A : Randomized k Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hm : A.MeasurableCoordinates) (hlaw : A.LazyLaw μ)
    (b : ℕ) (hb : 1≤b) (hk : 16*(b+1)≤k) (C : ℝ) (hC : 1≤C)
    (hkC : 66*C≤k) (hA : A.Restoration b) (hs : ∀a, (1:ℝ≥0∞)/2≤A.success μ a)
    (a₀ : Vertex k) :
    ¬(A.averageUpdates μ ≤ ENNReal.ofReal C * stationaryHitting μ (fun ω => A.increments ω 0) a₀ ∧
      A.averageChecks μ ≤ ENNReal.ofReal C / markedMass a₀) :=
  A.no_uniform_split μ hm.observable hlaw b hb hk C hC hkC hA hs a₀

end RandomWalkSearch.Cycle
