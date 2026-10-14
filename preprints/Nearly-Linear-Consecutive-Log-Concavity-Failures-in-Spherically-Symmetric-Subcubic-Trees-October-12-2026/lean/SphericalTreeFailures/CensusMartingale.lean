import SphericalTreeFailures.Broadcast
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # The conditional census martingale

All random variables in this file live on the explicit Bernoulli product space.
-/

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal ProbabilityTheory

noncomputable def occupation (i : Bool) (v : BinaryNode) (ω : BroadcastSpace) : ℝ :=
  boolIndicator (broadcastState i ω v)

noncomputable def inputValue (v : BinaryNode) (ω : BroadcastSpace) : ℝ :=
  boolIndicator (ω v)

noncomputable def centeredInput (p : ℝ) (v : BinaryNode) (ω : BroadcastSpace) : ℝ :=
  inputValue v ω - p

theorem measurable_occupation (i : Bool) (v : BinaryNode) : Measurable (occupation i v) :=
  measurable_boolIndicator.comp (measurable_broadcastState i v)

theorem measurable_occupation_at (i : Bool) (h : ℕ) (v : BinaryNode) (hv : v.length ≤ h) :
    @Measurable BroadcastSpace ℝ (inputFiltration h) inferInstance (occupation i v) :=
  measurable_boolIndicator.comp (measurable_broadcastState_at i h v hv)

theorem measurable_inputValue (v : BinaryNode) : Measurable (inputValue v) :=
  measurable_boolIndicator.comp (measurable_pi_apply v)

theorem memLp_bool_comp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f : Ω → Bool) (hf : Measurable f) (g : Bool → ℝ) (q : ℝ≥0∞) :
    MemLp (fun ω => g (f ω)) q μ := by
  apply MemLp.of_bound ((measurable_of_finite g).comp hf).aestronglyMeasurable
    (max ‖g false‖ ‖g true‖)
  exact ae_of_all _ fun ω => by cases h : f ω <;> simp [h]

theorem memLp_occupation (p : unitInterval) (i : Bool) (v : BinaryNode) (q : ℝ≥0∞) :
    MemLp (occupation i v) q (broadcastMeasure p) :=
  memLp_bool_comp _ _ (measurable_broadcastState i v) boolIndicator q

theorem memLp_inputValue (p : unitInterval) (v : BinaryNode) (q : ℝ≥0∞) :
    MemLp (inputValue v) q (broadcastMeasure p) :=
  memLp_bool_comp _ _ (measurable_pi_apply v) boolIndicator q

theorem integrable_occupation (p : unitInterval) (i : Bool) (v : BinaryNode) :
    Integrable (occupation i v) (broadcastMeasure p) :=
  memLp_one_iff_integrable.mp (memLp_occupation p i v 1)

theorem integrable_inputValue (p : unitInterval) (v : BinaryNode) :
    Integrable (inputValue v) (broadcastMeasure p) :=
  memLp_one_iff_integrable.mp (memLp_inputValue p v 1)

theorem integral_inputValue (p : unitInterval) (v : BinaryNode) :
    ∫ ω, inputValue v ω ∂broadcastMeasure p = p := by
  change ∫ ω, (boolIndicator ∘ (fun ω : BroadcastSpace => ω v)) ω ∂broadcastMeasure p = p
  rw [(broadcast_input_law p v).integral_comp measurable_boolIndicator.aestronglyMeasurable]
  simp [integral_bernoulliMeasure]

theorem condExp_inputValue (p : unitInterval) (h : ℕ) (v : BinaryNode) (hv : h < v.length) :
    (broadcastMeasure p)[inputValue v | inputFiltration h] =ᵐ[broadcastMeasure p]
      fun _ => (p : ℝ) := by
  have hm : @Measurable BroadcastSpace ℝ
      (MeasurableSpace.comap (fun ω : BroadcastSpace => ω v) inferInstance) inferInstance
      (inputValue v) := measurable_boolIndicator.comp (comap_measurable _)
  simpa only [integral_inputValue] using condExp_indep_eq
    (measurable_pi_apply v).comap_le (inputFiltration.le h)
    hm.stronglyMeasurable (fresh_input_independent p h v hv)

theorem condExp_occupation_child (p : unitInterval) (i : Bool) (h : ℕ)
    (b : Bool) (v : BinaryNode) (hv : v.length = h) :
    (broadcastMeasure p)[occupation i (b :: v) | inputFiltration h] =ᵐ[broadcastMeasure p]
      fun ω => (p : ℝ) * (1 - occupation i v ω) := by
  have hp : occupation i (b :: v) =
      (fun ω => 1 - occupation i v ω) * inputValue (b :: v) := by
    funext ω
    exact broadcast_indicator_child i ω b v
  have hm : StronglyMeasurable[inputFiltration h] (fun ω => 1 - occupation i v ω) :=
    (measurable_const.sub (measurable_occupation_at i h v hv.le)).stronglyMeasurable
  have hc := condExp_mul_of_stronglyMeasurable_left (μ := broadcastMeasure p) hm
    (hp ▸ integrable_occupation p i (b :: v)) (integrable_inputValue p (b :: v))
  rw [hp]
  filter_upwards [hc, condExp_inputValue p h (b :: v) (by simp [hv])] with ω hh hk
  simpa only [Pi.mul_apply, hk, mul_comm] using hh

theorem stationary_eigen_identity {p : ℝ} (hp : 0 ≤ p) (x : ℝ) :
    p * (1 - x) - stationaryProbability p = -p * (x - stationaryProbability p) := by
  unfold stationaryProbability
  have hh : 1 + p ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem measurable_census_at (p : ℝ) (i : Bool) (h : ℕ) :
    @Measurable BroadcastSpace ℝ (inputFiltration h) inferInstance (census p i h) := by
  unfold census
  exact Finset.measurable_sum _ fun v hv =>
    (measurable_occupation_at i h v ((mem_binaryLevel v h).mp hv).le).sub measurable_const

theorem memLp_census (p : unitInterval) (i : Bool) (h : ℕ) (q : ℝ≥0∞) :
    MemLp (census p i h) q (broadcastMeasure p) := by
  unfold census
  exact memLp_finsetSum (binaryLevel h) fun v _ =>
    (memLp_occupation p i v q).sub (memLp_const (stationaryProbability p))

theorem memLp_censusMartingale (p : unitInterval) (i : Bool) (h : ℕ) (q : ℝ≥0∞) :
    MemLp (censusMartingale p i h) q (broadcastMeasure p) := by
  exact (memLp_census p i h q).const_mul _

theorem integrable_census (p : unitInterval) (i : Bool) (h : ℕ) :
    Integrable (census p i h) (broadcastMeasure p) :=
  memLp_one_iff_integrable.mp (memLp_census p i h 1)

theorem integrable_censusMartingale (p : unitInterval) (i : Bool) (h : ℕ) :
    Integrable (censusMartingale p i h) (broadcastMeasure p) :=
  memLp_one_iff_integrable.mp (memLp_censusMartingale p i h 1)

theorem condExp_centered_occupation_child (p : unitInterval) (i : Bool) (h : ℕ)
    (b : Bool) (v : BinaryNode) (hv : v.length = h) :
    (broadcastMeasure p)[(fun ω => occupation i (b :: v) ω - stationaryProbability p) |
      inputFiltration h] =ᵐ[broadcastMeasure p]
      fun ω => -(p : ℝ) * (occupation i v ω - stationaryProbability p) := by
  have hh := condExp_sub (integrable_occupation p i (b :: v))
    (integrable_const (stationaryProbability p)) (inputFiltration h)
  filter_upwards [hh, condExp_occupation_child p i h b v hv] with ω he hx
  simp only [Pi.sub_apply, condExp_const (inputFiltration.le h), hx] at he
  exact he.trans (stationary_eigen_identity p.property.1 _)

theorem census_succ (p : ℝ) (i : Bool) (h : ℕ) :
    census p i (h + 1) =
      ∑ v ∈ binaryLevel h, ((fun ω => occupation i (false :: v) ω - stationaryProbability p) +
        (fun ω => occupation i (true :: v) ω - stationaryProbability p)) := by
  funext ω
  simpa only [census, occupation, Finset.sum_apply, Pi.add_apply] using
    sum_binaryLevel_succ (fun v => occupation i v ω - stationaryProbability p) h

theorem condExp_census_succ (p : unitInterval) (i : Bool) (h : ℕ) :
    (broadcastMeasure p)[census p i (h + 1) | inputFiltration h] =ᵐ[broadcastMeasure p]
      fun ω => -censusScale p * census p i h ω := by
  rw [census_succ]
  have hi (v : BinaryNode) (b : Bool) :
      Integrable (fun ω => occupation i (b :: v) ω - stationaryProbability p) (broadcastMeasure p) :=
    (integrable_occupation p i (b :: v)).sub (integrable_const _)
  have hs := condExp_finsetSum (fun v (_ : v ∈ binaryLevel h) => (hi v false).add (hi v true))
    (inputFiltration h)
  have hc (v : BinaryNode) (hv : v ∈ binaryLevel h) :
      (broadcastMeasure p)[((fun ω => occupation i (false :: v) ω - stationaryProbability p) +
        (fun ω => occupation i (true :: v) ω - stationaryProbability p)) | inputFiltration h]
        =ᵐ[broadcastMeasure p] fun ω => -censusScale p *
          (occupation i v ω - stationaryProbability p) := by
    have hl := (mem_binaryLevel v h).mp hv
    filter_upwards [condExp_add (hi v false) (hi v true) (inputFiltration h),
      condExp_centered_occupation_child p i h false v hl,
      condExp_centered_occupation_child p i h true v hl] with ω ha hb hc
    simp only [Pi.add_apply, hb, hc] at ha
    exact ha.trans (by unfold censusScale; ring)
  have he : (∑ v ∈ binaryLevel h, (broadcastMeasure p)[((fun ω => occupation i (false :: v) ω - stationaryProbability p) +
        (fun ω => occupation i (true :: v) ω - stationaryProbability p)) | inputFiltration h])
      =ᵐ[broadcastMeasure p] ∑ v ∈ binaryLevel h,
        (fun ω => -censusScale p * (occupation i v ω - stationaryProbability p)) :=
    eventuallyEq_sum fun v hv => hc v hv
  refine hs.trans (he.trans ?_)
  exact ae_of_all _ fun ω => by simp only [census, occupation, Finset.sum_apply, ← Finset.mul_sum]

/-- The normalized census is a martingale on the actual infinite product space. -/
theorem census_is_martingale (p : unitInterval) (hp : 0 < (p : ℝ)) (i : Bool) :
    Martingale (censusMartingale p i) inputFiltration (broadcastMeasure p) := by
  apply martingale_nat
  · intro h
    exact (measurable_const.mul (measurable_census_at p i h)).stronglyMeasurable
  · exact integrable_censusMartingale p i
  · intro h
    have he := condExp_smul (μ := broadcastMeasure p)
      (((-censusScale p) ^ (h + 1))⁻¹) (census p i (h + 1)) (inputFiltration h)
    have hn : censusScale p ≠ 0 := by unfold censusScale; positivity
    filter_upwards [he, condExp_census_succ p i h] with ω ha hb
    change (broadcastMeasure p)[censusMartingale p i (h + 1) | inputFiltration h] ω =
      (((-censusScale p) ^ (h + 1))⁻¹) *
        (broadcastMeasure p)[census p i (h + 1) | inputFiltration h] ω at ha
    rw [ha, hb]
    unfold censusMartingale
    rw [pow_succ, mul_inv_rev]
    field_simp

theorem integral_censusMartingale (p : unitInterval) (hp : 0 < (p : ℝ)) (i : Bool) (h : ℕ) :
    ∫ ω, censusMartingale p i h ω ∂broadcastMeasure p =
      boolIndicator i - stationaryProbability p := by
  have he := (census_is_martingale p hp i).setIntegral_eq (Nat.zero_le h) MeasurableSet.univ
  simpa using he.symm

theorem memLp_centeredInput (p : unitInterval) (v : BinaryNode) (q : ℝ≥0∞) :
    MemLp (centeredInput p v) q (broadcastMeasure p) :=
  (memLp_inputValue p v q).sub (memLp_const _)

theorem integral_centeredInput (p : unitInterval) (v : BinaryNode) :
    ∫ ω, centeredInput p v ω ∂broadcastMeasure p = 0 := by
  simp [centeredInput, integral_sub (integrable_inputValue p v) (integrable_const (p : ℝ)),
    integral_inputValue]

theorem integral_centeredInput_sq (p : unitInterval) (v : BinaryNode) :
    ∫ ω, (centeredInput p v ω) ^ 2 ∂broadcastMeasure p = (p : ℝ) * (1 - p) := by
  have he := (broadcast_input_law p v).integral_comp
    (measurable_of_finite (fun b => (boolIndicator b - (p : ℝ)) ^ 2)).aestronglyMeasurable
  change (∫ ω, (centeredInput p v ω) ^ 2 ∂broadcastMeasure p) = _ at he
  rw [he, integral_bernoulliMeasure]
  simp only [boolIndicator_true, boolIndicator_false, smul_eq_mul]
  ring

theorem integral_centeredInput_mul (p : unitInterval) (u v : BinaryNode) (huv : u ≠ v) :
    ∫ ω, centeredInput p u ω * centeredInput p v ω ∂broadcastMeasure p = 0 := by
  have hind := ((broadcast_inputs_independent p).indepFun huv).comp
    (measurable_of_finite (fun b => boolIndicator b - (p : ℝ)))
    (measurable_of_finite (fun b => boolIndicator b - (p : ℝ)))
  have he := hind.integral_mul_eq_mul_integral
    (memLp_centeredInput p u 1).aestronglyMeasurable
    (memLp_centeredInput p v 1).aestronglyMeasurable
  change (∫ ω, centeredInput p u ω * centeredInput p v ω ∂broadcastMeasure p) =
    (∫ ω, centeredInput p u ω ∂broadcastMeasure p) *
      (∫ ω, centeredInput p v ω ∂broadcastMeasure p) at he
  simpa only [integral_centeredInput, mul_zero] using he

theorem condExp_future (p : unitInterval) (h : ℕ) {S : Set BinaryNode}
    (hS : ∀ v ∈ S, h < v.length) {f : BroadcastSpace → ℝ}
    (hf : StronglyMeasurable[inputSigma S] f) :
    (broadcastMeasure p)[f | inputFiltration h] =ᵐ[broadcastMeasure p]
      fun _ => ∫ ω, f ω ∂broadcastMeasure p := by
  have hd : Disjoint S {v : BinaryNode | v.length ≤ h} := by
    rw [Set.disjoint_left]
    exact fun v hv hh => (not_le.mpr (hS v hv)) hh
  exact condExp_indep_eq (inputSigma_le S) (inputFiltration.le h) hf
    (inputSigma_independent p hd)

theorem condExp_centeredInput_mul (p : unitInterval) (h : ℕ) (u v : BinaryNode)
    (hu : h < u.length) (hv : h < v.length) :
    (broadcastMeasure p)[(fun ω => centeredInput p u ω * centeredInput p v ω) |
      inputFiltration h] =ᵐ[broadcastMeasure p]
      fun _ => if u = v then (p : ℝ) * (1 - p) else 0 := by
  have hm (w : BinaryNode) (hw : w ∈ ({u, v} : Set BinaryNode)) :
      @Measurable BroadcastSpace ℝ (inputSigma {u, v}) inferInstance (centeredInput p w) :=
    (measurable_boolIndicator.comp (measurable_input_in hw)).sub measurable_const
  have hs : ∀ w ∈ ({u, v} : Set BinaryNode), h < w.length := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;> assumption
  have he := condExp_future p h hs
    ((hm u (by simp)).mul (hm v (by simp))).stronglyMeasurable
  change (broadcastMeasure p)[(fun ω => centeredInput p u ω * centeredInput p v ω) |
    inputFiltration h] =ᵐ[broadcastMeasure p] fun _ =>
      ∫ ω, centeredInput p u ω * centeredInput p v ω ∂broadcastMeasure p at he
  have hint : (∫ ω, centeredInput p u ω * centeredInput p v ω ∂broadcastMeasure p) =
      if u = v then (p : ℝ) * (1 - p) else 0 := by
    by_cases huv : u = v
    · subst v
      simpa only [← pow_two, ite_true] using integral_centeredInput_sq p u
    · simpa only [huv, ite_false] using integral_centeredInput_mul p u v huv
  simpa only [hint] using he

end SphericalTreeFailures
