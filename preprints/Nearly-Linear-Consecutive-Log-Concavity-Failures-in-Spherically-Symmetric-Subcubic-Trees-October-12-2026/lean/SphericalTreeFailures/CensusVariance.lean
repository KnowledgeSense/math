import SphericalTreeFailures.CensusMartingale

/-! # Conditional innovation variances

Fresh input coordinates are independent both of earlier generations and of one
another. Their exact covariance calculation gives the census increment variance.
-/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal ProbabilityTheory

noncomputable def parentVacancy (i : Bool) (v : BinaryNode) (ω : BroadcastSpace) : ℝ :=
  1 - occupation i v.tail ω

noncomputable def innovation (p : ℝ) (i : Bool) (v : BinaryNode) (ω : BroadcastSpace) : ℝ :=
  parentVacancy i v ω * centeredInput p v ω

theorem parentVacancy_sq (i : Bool) (v : BinaryNode) (ω : BroadcastSpace) :
    parentVacancy i v ω ^ 2 = parentVacancy i v ω := by
  unfold parentVacancy occupation
  cases hh : broadcastState i ω v.tail <;> norm_num [hh]

theorem measurable_parentVacancy (i : Bool) (v : BinaryNode) : Measurable (parentVacancy i v) :=
  measurable_const.sub (measurable_occupation i v.tail)

theorem measurable_parentVacancy_at (i : Bool) (h : ℕ) (v : BinaryNode) (hv : v.length = h + 1) :
    @Measurable BroadcastSpace ℝ (inputFiltration h) inferInstance (parentVacancy i v) := by
  apply measurable_const.sub
  apply measurable_occupation_at
  simp [List.length_tail, hv]

theorem measurable_centeredInput (p : ℝ) (v : BinaryNode) : Measurable (centeredInput p v) :=
  (measurable_inputValue v).sub measurable_const

theorem memLp_innovation (p : unitInterval) (i : Bool) (v : BinaryNode) (q : ℝ≥0∞) :
    MemLp (innovation p i v) q (broadcastMeasure p) := by
  apply MemLp.of_bound ((measurable_parentVacancy i v).mul
    (measurable_centeredInput p v)).aestronglyMeasurable 1
  refine ae_of_all _ fun ω => ?_
  change ‖innovation p i v ω‖ ≤ 1
  unfold innovation parentVacancy occupation centeredInput inputValue
  have hp0 := p.property.1
  have hp1 := p.property.2
  cases hs : broadcastState i ω v.tail <;> cases hv : ω v <;>
    simp [abs_of_nonneg hp0, abs_of_nonneg (sub_nonneg.mpr hp1)] <;> linarith

theorem condExp_innovation_mul (p : unitInterval) (i : Bool) (h : ℕ)
    (u v : BinaryNode) (hu : u.length = h + 1) (hv : v.length = h + 1) :
    (broadcastMeasure p)[(fun ω => innovation p i u ω * innovation p i v ω) |
      inputFiltration h] =ᵐ[broadcastMeasure p]
      fun ω => if u = v then (p : ℝ) * (1 - p) * parentVacancy i u ω else 0 := by
  let a : BroadcastSpace → ℝ := fun ω => parentVacancy i u ω * parentVacancy i v ω
  let b : BroadcastSpace → ℝ := fun ω => centeredInput p u ω * centeredInput p v ω
  have heq : (fun ω => innovation p i u ω * innovation p i v ω) = a * b := by
    funext ω
    dsimp [a, b, innovation]
    ring
  have ha : StronglyMeasurable[inputFiltration h] a :=
    ((measurable_parentVacancy_at i h u hu).mul
      (measurable_parentVacancy_at i h v hv)).stronglyMeasurable
  have hab : Integrable (a * b) (broadcastMeasure p) :=
    heq ▸ (memLp_innovation p i u 2).integrable_mul (memLp_innovation p i v 2)
  have hb : Integrable b (broadcastMeasure p) :=
    (memLp_centeredInput p u 2).integrable_mul (memLp_centeredInput p v 2)
  have hpull := condExp_mul_of_stronglyMeasurable_left ha hab hb
  rw [heq]
  filter_upwards [hpull, condExp_centeredInput_mul p h u v (by omega) (by omega)] with ω hx hy
  change (broadcastMeasure p)[a * b | inputFiltration h] ω = a ω *
    (broadcastMeasure p)[b | inputFiltration h] ω at hx
  rw [hx]
  change a ω * (broadcastMeasure p)[(fun ω => centeredInput p u ω * centeredInput p v ω) |
    inputFiltration h] ω = _
  rw [hy]
  by_cases huv : u = v
  · subst v
    simp only [ite_true, a]
    rw [← pow_two, parentVacancy_sq]
    ring
  · simp [huv]

theorem innovation_child (p : unitInterval) (i : Bool) (b : Bool) (v : BinaryNode)
    (ω : BroadcastSpace) :
    innovation p i (b :: v) ω =
      occupation i (b :: v) ω - stationaryProbability p +
        (p : ℝ) * (occupation i v ω - stationaryProbability p) := by
  have he := stationary_eigen_identity p.property.1 (occupation i v ω)
  have hc := broadcast_indicator_child i ω b v
  change occupation i (b :: v) ω = (1 - occupation i v ω) * inputValue (b :: v) ω at hc
  unfold innovation parentVacancy centeredInput
  simp only [List.tail_cons]
  nlinarith

theorem innovation_sum (p : unitInterval) (i : Bool) (h : ℕ) (ω : BroadcastSpace) :
    ∑ v ∈ binaryLevel (h + 1), innovation p i v ω =
      census p i (h + 1) ω + censusScale p * census p i h ω := by
  rw [sum_binaryLevel_succ, census_succ]
  simp only [Finset.sum_apply, Pi.add_apply]
  change _ = _ + censusScale p *
    ∑ v ∈ binaryLevel h, (occupation i v ω - stationaryProbability p)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [innovation_child, innovation_child]
  unfold censusScale
  ring

theorem census_increment (p : unitInterval) (hp : 0 < (p : ℝ)) (i : Bool) (h : ℕ)
    (ω : BroadcastSpace) :
    censusMartingale p i (h + 1) ω - censusMartingale p i h ω =
      ((-censusScale p) ^ (h + 1))⁻¹ * ∑ v ∈ binaryLevel (h + 1), innovation p i v ω := by
  rw [innovation_sum]
  unfold censusMartingale
  have hg : censusScale p ≠ 0 := by unfold censusScale; positivity
  rw [pow_succ]
  field_simp
  ring

/-- Conditional second moments of a finite sum are the sum of its conditional
mixed second moments. -/
theorem condExp_sum_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (m : MeasurableSpace Ω) {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ j ∈ s, MemLp (f j) 2 μ) :
    μ[(fun ω => (∑ j ∈ s, f j ω) ^ 2) | m] =ᵐ[μ]
      ∑ j ∈ s, ∑ k ∈ s, μ[(fun ω => f j ω * f k ω) | m] := by
  have he : (fun ω => (∑ j ∈ s, f j ω) ^ 2) =
      ∑ j ∈ s, ∑ k ∈ s, (fun ω => f j ω * f k ω) := by
    funext ω
    simp only [Finset.sum_apply, pow_two, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [he]
  refine (condExp_finsetSum (fun j hj =>
    integrable_finsetSum' s (fun k hk => (hf j hj).integrable_mul (hf k hk))) m).trans ?_
  exact eventuallyEq_sum fun j hj =>
    condExp_finsetSum (fun k hk => (hf j hj).integrable_mul (hf k hk)) m

theorem condExp_innovation_sum_sq (p : unitInterval) (i : Bool) (h : ℕ) :
    (broadcastMeasure p)[(fun ω => (∑ v ∈ binaryLevel (h + 1), innovation p i v ω) ^ 2) |
      inputFiltration h] =ᵐ[broadcastMeasure p]
      fun ω => (p : ℝ) * (1 - p) * ∑ v ∈ binaryLevel (h + 1), parentVacancy i v ω := by
  refine (condExp_sum_sq (broadcastMeasure p) (inputFiltration h) (binaryLevel (h + 1))
    (innovation p i) (fun v _ => memLp_innovation p i v 2)).trans ?_
  have he : (∑ u ∈ binaryLevel (h + 1), ∑ v ∈ binaryLevel (h + 1),
      (broadcastMeasure p)[(fun ω => innovation p i u ω * innovation p i v ω) |
        inputFiltration h]) =ᵐ[broadcastMeasure p]
      ∑ u ∈ binaryLevel (h + 1), ∑ v ∈ binaryLevel (h + 1),
        (fun ω => if u = v then (p : ℝ) * (1 - p) * parentVacancy i u ω else 0) :=
    eventuallyEq_sum fun u hu => eventuallyEq_sum fun v hv =>
      condExp_innovation_mul p i h u v ((mem_binaryLevel _ _).mp hu) ((mem_binaryLevel _ _).mp hv)
  refine he.trans (ae_of_all _ fun ω => ?_)
  simp only [Finset.sum_apply]
  simp only [Finset.sum_ite_eq]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u hu => by simp [hu]

theorem normalized_square_factor (g : ℝ) (h : ℕ) :
    (((-g) ^ h)⁻¹) ^ 2 = (g ^ (2 * h))⁻¹ := by
  calc
    (((-g) ^ h)⁻¹) ^ 2 = (((-g) ^ h) ^ 2)⁻¹ := by rw [inv_pow]
    _ = (g ^ (2 * h))⁻¹ := by
      congr 1
      rw [← pow_mul, Nat.mul_comm h 2, pow_mul, neg_sq, ← pow_mul]

theorem conditional_census_increment_variance (p : unitInterval) (hp : 0 < (p : ℝ))
    (i : Bool) (h : ℕ) :
    (broadcastMeasure p)[(fun ω =>
      (censusMartingale p i (h + 1) ω - censusMartingale p i h ω) ^ 2) |
        inputFiltration h] =ᵐ[broadcastMeasure p]
      fun ω => (censusScale p ^ (2 * (h + 1)))⁻¹ * (p : ℝ) * (1 - p) *
        ∑ v ∈ binaryLevel (h + 1), parentVacancy i v ω := by
  have he : (fun ω => (censusMartingale p i (h + 1) ω - censusMartingale p i h ω) ^ 2) =
      (censusScale p ^ (2 * (h + 1)))⁻¹ •
        (fun ω => (∑ v ∈ binaryLevel (h + 1), innovation p i v ω) ^ 2) := by
    funext ω
    rw [census_increment p hp i h ω, mul_pow, normalized_square_factor]
    rfl
  rw [he]
  filter_upwards [condExp_smul (μ := broadcastMeasure p)
    ((censusScale p ^ (2 * (h + 1)))⁻¹)
      (fun ω => (∑ v ∈ binaryLevel (h + 1), innovation p i v ω) ^ 2) (inputFiltration h),
    condExp_innovation_sum_sq p i h] with ω ha hb
  simp only [Pi.smul_apply, smul_eq_mul, hb] at ha
  exact ha.trans (by ring)

theorem parentVacancy_bounds (i : Bool) (v : BinaryNode) (ω : BroadcastSpace) :
    0 ≤ parentVacancy i v ω ∧ parentVacancy i v ω ≤ 1 := by
  unfold parentVacancy occupation
  constructor
  · exact sub_nonneg.mpr (boolIndicator_le_one _)
  · linarith [boolIndicator_nonneg (broadcastState i ω v.tail)]

theorem variance_factor_identity (p : ℝ) (hp : 0 < p) (h : ℕ) :
    (censusScale p ^ (2 * h))⁻¹ * p * (1 - p) * (2 : ℝ) ^ h =
      p * (1 - p) * ((2 * p ^ 2) ^ h)⁻¹ := by
  have hg : censusScale p ^ 2 = 2 * (2 * p ^ 2) := by unfold censusScale; ring
  rw [pow_mul, hg, mul_pow]
  have hn : p ≠ 0 := ne_of_gt hp
  field_simp

theorem conditional_census_increment_bound (p : unitInterval) (hp : 0 < (p : ℝ))
    (i : Bool) (h : ℕ) :
    (broadcastMeasure p)[(fun ω =>
      (censusMartingale p i (h + 1) ω - censusMartingale p i h ω) ^ 2) |
        inputFiltration h] ≤ᵐ[broadcastMeasure p]
      fun _ => (p : ℝ) * (1 - p) * ((2 * (p : ℝ) ^ 2) ^ (h + 1))⁻¹ := by
  filter_upwards [conditional_census_increment_variance p hp i h] with ω he
  rw [he, ← variance_factor_identity p hp (h + 1)]
  apply mul_le_mul_of_nonneg_left
  · calc
      (∑ v ∈ binaryLevel (h + 1), parentVacancy i v ω) ≤
          ∑ _v ∈ binaryLevel (h + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun v _ => (parentVacancy_bounds i v ω).2
      _ = (2 : ℝ) ^ (h + 1) := by simp
  · have hp1 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.property.2
    unfold censusScale
    positivity

theorem integrable_census_increment_sq (p : unitInterval) (i : Bool) (h : ℕ) :
    Integrable (fun ω =>
      (censusMartingale p i (h + 1) ω - censusMartingale p i h ω) ^ 2)
        (broadcastMeasure p) := by
  have hm := (memLp_censusMartingale p i (h + 1) 2).sub (memLp_censusMartingale p i h 2)
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm

theorem integral_census_increment_sq_bound (p : unitInterval) (hp : 0 < (p : ℝ))
    (i : Bool) (h : ℕ) :
    (∫ ω, (censusMartingale p i (h + 1) ω - censusMartingale p i h ω) ^ 2
      ∂broadcastMeasure p) ≤
      (p : ℝ) * (1 - p) * ((2 * (p : ℝ) ^ 2) ^ (h + 1))⁻¹ := by
  have he := integral_mono_ae (μ := broadcastMeasure p) integrable_condExp
    (integrable_const _) (conditional_census_increment_bound p hp i h)
  simpa [integral_condExp (inputFiltration.le h), integral_const,
    one_smul] using he

end SphericalTreeFailures
