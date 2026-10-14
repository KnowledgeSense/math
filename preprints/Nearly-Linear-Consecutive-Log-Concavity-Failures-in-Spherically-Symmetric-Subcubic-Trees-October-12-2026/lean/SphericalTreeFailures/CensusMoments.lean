import SphericalTreeFailures.CensusLimit
import Mathlib.Probability.Moments.Variance

/-! # Means and variances of the census limit -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal ProbabilityTheory Topology

noncomputable def l2Constant {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (c : ℝ) : Lp ℝ 2 μ :=
  (memLp_const c).toLp (fun _ => c)

theorem inner_l2Constant_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    inner ℝ f (l2Constant μ 1) = ∫ ω, f ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_const (p := (2 : ℝ≥0∞)) (μ := μ) (1 : ℝ)).coeFn_toLp] with ω hω
  change inner ℝ (f ω) ((memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ)) ω) = _
  change ((memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ)) ω) * f ω = f ω
  rw [hω, one_mul]

theorem integral_censusLimit (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    ∫ ω, censusLimit p i ω ∂broadcastMeasure p = boolIndicator i - stationaryProbability p := by
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  have ht := (censusL2_tendsto p hc i).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := l2Constant (broadcastMeasure p) 1))
  have he (h : ℕ) : inner ℝ (censusL2 p i h) (l2Constant (broadcastMeasure p) 1) =
      boolIndicator i - stationaryProbability p := by
    rw [inner_l2Constant_one]
    exact (integral_congr_ae (memLp_censusMartingale p i h 2).coeFn_toLp).trans
      (integral_censusMartingale p hp i h)
  simp only [he] at ht
  have hh := tendsto_nhds_unique ht tendsto_const_nhds
  simpa only [inner_l2Constant_one, censusLimit] using hh

theorem condExp_census_increment_zero (p : unitInterval) (hp : 0 < (p : ℝ))
    (i : Bool) (h : ℕ) :
    (broadcastMeasure p)[censusMartingale p i (h + 1) - censusMartingale p i h |
      inputFiltration h] =ᵐ[broadcastMeasure p] 0 := by
  have hm := census_is_martingale p hp i
  have ha := hm.condExp_ae_eq (Nat.le_succ h)
  have hb : (broadcastMeasure p)[censusMartingale p i h | inputFiltration h] =
      censusMartingale p i h :=
    condExp_of_stronglyMeasurable (inputFiltration.le h) (hm.stronglyAdapted h) (hm.integrable h)
  filter_upwards [condExp_sub (hm.integrable (h + 1)) (hm.integrable h) (inputFiltration h), ha]
    with ω hx hy
  simpa only [Pi.sub_apply, Pi.zero_apply, hb, hy, sub_self] using hx

theorem integral_predictable_mul_increment (p : unitInterval) (hp : 0 < (p : ℝ))
    (i : Bool) (h : ℕ) (g : BroadcastSpace → ℝ)
    (hg : StronglyMeasurable[inputFiltration h] g) (hg2 : MemLp g 2 (broadcastMeasure p)) :
    ∫ ω, g ω * (censusMartingale p i (h + 1) ω - censusMartingale p i h ω)
      ∂broadcastMeasure p = 0 := by
  have hm := (memLp_censusMartingale p i (h + 1) 2).sub (memLp_censusMartingale p i h 2)
  have he := condExp_mul_of_stronglyMeasurable_left hg (hg2.integrable_mul hm)
    ((integrable_censusMartingale p i (h + 1)).sub (integrable_censusMartingale p i h))
  have hz : (broadcastMeasure p)[g * (censusMartingale p i (h + 1) - censusMartingale p i h) |
      inputFiltration h] =ᵐ[broadcastMeasure p] 0 := by
    filter_upwards [he, condExp_census_increment_zero p hp i h] with ω ha hb
    simpa only [Pi.mul_apply, Pi.zero_apply, hb, mul_zero] using ha
  rw [← integral_condExp (inputFiltration.le h)]
  exact (integral_congr_ae hz).trans (by simp)

theorem censusL2_increment_orthogonal (p : unitInterval) (hp : 0 < (p : ℝ))
    (i : Bool) (h : ℕ) :
    inner ℝ (censusL2 p i h - censusL2 p i 0)
      (censusL2 p i (h + 1) - censusL2 p i h) = 0 := by
  rw [L2.inner_def]
  have hA := ((memLp_censusMartingale p i h 2).sub (memLp_censusMartingale p i 0 2)).coeFn_toLp
  have hB := ((memLp_censusMartingale p i (h + 1) 2).sub (memLp_censusMartingale p i h 2)).coeFn_toLp
  have he : (∫ ω, inner ℝ ((censusL2 p i h - censusL2 p i 0) ω)
      ((censusL2 p i (h + 1) - censusL2 p i h) ω) ∂broadcastMeasure p) =
      ∫ ω, (censusMartingale p i h ω - censusMartingale p i 0 ω) *
        (censusMartingale p i (h + 1) ω - censusMartingale p i h ω) ∂broadcastMeasure p := by
    apply integral_congr_ae
    filter_upwards [hA, hB] with ω ha hb
    change (censusL2 p i h - censusL2 p i 0) ω = _ at ha
    change (censusL2 p i (h + 1) - censusL2 p i h) ω = _ at hb
    rw [ha, hb]
    change (censusMartingale p i (h + 1) ω - censusMartingale p i h ω) *
      (censusMartingale p i h ω - censusMartingale p i 0 ω) = _
    ring
  rw [he]
  apply integral_predictable_mul_increment p hp i h
  · have hm := (census_is_martingale p hp i).stronglyAdapted h
    have hh : censusMartingale p i 0 =
        (fun _ => boolIndicator i - stationaryProbability p) := by funext ω; simp
    rw [hh]
    exact hm.sub stronglyMeasurable_const
  · exact (memLp_censusMartingale p i h 2).sub (memLp_censusMartingale p i 0 2)

theorem censusL2_centered_sq_succ (p : unitInterval) (hp : 0 < (p : ℝ))
    (i : Bool) (h : ℕ) :
    ‖censusL2 p i (h + 1) - censusL2 p i 0‖ ^ 2 =
      ‖censusL2 p i h - censusL2 p i 0‖ ^ 2 +
        ‖censusL2 p i (h + 1) - censusL2 p i h‖ ^ 2 := by
  have he : censusL2 p i (h + 1) - censusL2 p i 0 =
      (censusL2 p i h - censusL2 p i 0) +
        (censusL2 p i (h + 1) - censusL2 p i h) := by abel
  rw [he, norm_add_sq_real, censusL2_increment_orthogonal p hp i h]
  ring

theorem geometric_variance_recursion (A d : ℝ) (hd : 1 < d) (h : ℕ) :
    A / (d - 1) * (1 - (d ^ h)⁻¹) + A * (d ^ (h + 1))⁻¹ =
      A / (d - 1) * (1 - (d ^ (h + 1))⁻¹) := by
  have hd0 : d ≠ 0 := ne_of_gt (by linarith)
  have hd1 : d - 1 ≠ 0 := ne_of_gt (by linarith)
  rw [pow_succ]
  field_simp
  ring

theorem censusL2_centered_sq_bound_refined (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (i : Bool) (h : ℕ) :
    ‖censusL2 p i h - censusL2 p i 0‖ ^ 2 ≤
      (p : ℝ) * (1 - p) / (2 * (p : ℝ) ^ 2 - 1) *
        (1 - ((2 * (p : ℝ) ^ 2) ^ h)⁻¹) := by
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  induction h with
  | zero => simp
  | succ h ih =>
    rw [censusL2_centered_sq_succ p hp i h]
    calc
      _ ≤ (p : ℝ) * (1 - p) / (2 * (p : ℝ) ^ 2 - 1) *
          (1 - ((2 * (p : ℝ) ^ 2) ^ h)⁻¹) +
            (p : ℝ) * (1 - p) * ((2 * (p : ℝ) ^ 2) ^ (h + 1))⁻¹ := by
        apply add_le_add ih
        rw [censusL2_increment_sq]
        exact integral_census_increment_sq_bound p hp i h
      _ = _ := geometric_variance_recursion _ _ hc h

theorem censusL2_centered_sq_bound (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (i : Bool) (h : ℕ) :
    ‖censusL2 p i h - censusL2 p i 0‖ ^ 2 ≤
      (p : ℝ) * (1 - p) / (2 * (p : ℝ) ^ 2 - 1) := by
  refine (censusL2_centered_sq_bound_refined p hc i h).trans ?_
  apply mul_le_of_le_one_right
  · exact div_nonneg (mul_nonneg p.property.1 (sub_nonneg.mpr p.property.2)) (by linarith)
  · have hh : 0 ≤ ((2 * (p : ℝ) ^ 2) ^ h)⁻¹ := by positivity
    linarith

theorem censusLimitL2_centered_sq_bound (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (i : Bool) :
    ‖censusLimitL2 p i - censusL2 p i 0‖ ^ 2 ≤
      (p : ℝ) * (1 - p) / (2 * (p : ℝ) ^ 2 - 1) := by
  apply le_of_tendsto (((censusL2_tendsto p hc i).sub
    (tendsto_const_nhds (x := censusL2 p i 0))).norm.pow 2)
  exact Eventually.of_forall (censusL2_centered_sq_bound p hc i)

theorem norm_L2_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by simp [pow_two]

theorem variance_censusLimit_eq_norm (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (i : Bool) :
    Var[censusLimit p i; broadcastMeasure p] = ‖censusLimitL2 p i - censusL2 p i 0‖ ^ 2 := by
  rw [variance_eq_integral (memLp_censusLimit p i).aemeasurable,
    integral_censusLimit p hc i, norm_L2_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (censusLimitL2 p i) (censusL2 p i 0),
    (memLp_censusMartingale p i 0 2).coeFn_toLp] with ω hs h0
  change (censusL2 p i 0) ω = _ at h0
  rw [hs]
  dsimp only [Pi.sub_apply]
  rw [h0, censusMartingale_zero]
  rfl

theorem variance_censusLimit_bound (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (i : Bool) :
    Var[censusLimit p i; broadcastMeasure p] ≤
      (p : ℝ) * (1 - p) / (2 * (p : ℝ) ^ 2 - 1) := by
  rw [variance_censusLimit_eq_norm p hc i]
  exact censusLimitL2_centered_sq_bound p hc i

theorem sharp_variance_bound {p : ℝ} (hp : 99 / 100 < p) (hp1 : p ≤ 1) :
    p * (1 - p) / (2 * p ^ 2 - 1) ≤ 2 * (1 - p) := by
  have hd : 0 < 2 * p ^ 2 - 1 := by nlinarith
  apply (div_le_iff₀ hd).mpr
  have he : p ≤ 2 * (2 * p ^ 2 - 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hp1)]

theorem censusL2_centered_sq_monotone (p : unitInterval) (hp : 0 < (p : ℝ)) (i : Bool) :
    Monotone (fun h => ‖censusL2 p i h - censusL2 p i 0‖ ^ 2) := by
  apply monotone_nat_of_le_succ
  intro h
  rw [censusL2_centered_sq_succ p hp i h]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem censusL2_centered_sq_le_limit (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (i : Bool) (h : ℕ) :
    ‖censusL2 p i h - censusL2 p i 0‖ ^ 2 ≤ ‖censusLimitL2 p i - censusL2 p i 0‖ ^ 2 := by
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  apply ge_of_tendsto (((censusL2_tendsto p hc i).sub
    (tendsto_const_nhds (x := censusL2 p i 0))).norm.pow 2)
  exact (eventually_ge_atTop h).mono fun k hk => censusL2_centered_sq_monotone p hp i hk

theorem vacant_parents_root_zero (ω : BroadcastSpace) :
    ∑ v ∈ binaryLevel 1, parentVacancy false v ω = 2 := by
  rw [sum_binaryLevel_succ _ 0]
  norm_num [binaryLevel, parentVacancy, occupation]

theorem vacant_parents_root_one (ω : BroadcastSpace) :
    ∑ v ∈ binaryLevel 2, parentVacancy true v ω = 4 := by
  rw [sum_binaryLevel_succ _ 1, sum_binaryLevel_succ _ 0]
  norm_num [binaryLevel, parentVacancy, occupation]

theorem first_variance_positive (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < ‖censusL2 p false 1 - censusL2 p false 0‖ ^ 2 := by
  rw [censusL2_increment_sq]
  have hce := conditional_census_increment_variance p hp false 0
  simp only [Nat.zero_add, Nat.mul_one, vacant_parents_root_zero] at hce
  have he := integral_congr_ae hce
  rw [integral_condExp (inputFiltration.le 0)] at he
  simp only [integral_const, probReal_univ, one_smul] at he
  rw [he]
  have hg : 0 < censusScale p := by unfold censusScale; positivity
  positivity

theorem second_variance_positive (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < ‖censusL2 p true 2 - censusL2 p true 1‖ ^ 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, censusL2_increment_sq]
  have hce := conditional_census_increment_variance p hp true 1
  norm_num only [Nat.reduceAdd, Nat.reduceMul] at hce
  simp only [vacant_parents_root_one] at hce
  have he := integral_congr_ae hce
  rw [integral_condExp (inputFiltration.le 1)] at he
  simp only [integral_const, probReal_univ, one_smul] at he
  rw [he]
  have hg : 0 < censusScale p := by unfold censusScale; positivity
  positivity

theorem variance_censusLimit_pos (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (i : Bool) : 0 < Var[censusLimit p i; broadcastMeasure p] := by
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  rw [variance_censusLimit_eq_norm p hc i]
  cases i with
  | false => exact (first_variance_positive p hp hp1).trans_le (censusL2_centered_sq_le_limit p hc false 1)
  | true =>
    have hs := censusL2_centered_sq_succ p hp true 1
    have hp' := second_variance_positive p hp hp1
    have h0 := sq_nonneg ‖censusL2 p true 1 - censusL2 p true 0‖
    have hh : 0 < ‖censusL2 p true 2 - censusL2 p true 0‖ ^ 2 := by nlinarith
    exact hh.trans_le (censusL2_centered_sq_le_limit p hc true 2)

theorem variance_census_eq_norm (p : unitInterval) (hp : 0 < (p : ℝ)) (i : Bool) (h : ℕ) :
    Var[censusMartingale p i h; broadcastMeasure p] = ‖censusL2 p i h - censusL2 p i 0‖ ^ 2 := by
  rw [variance_eq_integral (memLp_censusMartingale p i h 2).aemeasurable,
    integral_censusMartingale p hp i h]
  have he := norm_toLp_sq (broadcastMeasure p)
    (censusMartingale p i h - censusMartingale p i 0)
    ((memLp_censusMartingale p i h 2).sub (memLp_censusMartingale p i 0 2))
  change ‖censusL2 p i h - censusL2 p i 0‖ ^ 2 = _ at he
  simpa only [Pi.sub_apply, censusMartingale_zero] using he.symm

theorem stationaryProbability_bounds (p : unitInterval) :
    0 ≤ stationaryProbability p ∧ stationaryProbability p ≤ 1 := by
  have hd : 0 < 1 + (p : ℝ) := by linarith [p.property.1]
  unfold stationaryProbability
  exact ⟨div_nonneg p.property.1 hd.le, (div_le_one hd).mpr (by linarith)⟩

theorem census_initial_sq_le_one (p : unitInterval) (i : Bool) :
    (boolIndicator i - stationaryProbability p) ^ 2 ≤ 1 := by
  obtain ⟨hl, hu⟩ := stationaryProbability_bounds p
  cases i <;> simp only [boolIndicator_false, boolIndicator_true] <;> nlinarith

theorem census_second_moment_le_two (p : unitInterval) (hp : 99 / 100 < (p : ℝ))
    (i : Bool) (h : ℕ) :
    ∫ ω, censusMartingale p i h ω ^ 2 ∂broadcastMeasure p ≤ 2 := by
  have hp0 : 0 < (p : ℝ) := by linarith
  have hc : 1 < 2 * (p : ℝ) ^ 2 := by nlinarith
  have hv := (censusL2_centered_sq_bound p hc i h).trans (sharp_variance_bound hp p.property.2)
  rw [← variance_census_eq_norm p hp0 i h, variance_eq_sub (memLp_censusMartingale p i h 2),
    integral_censusMartingale p hp0 i h] at hv
  change (∫ ω, censusMartingale p i h ω ^ 2 ∂broadcastMeasure p) -
    (boolIndicator i - stationaryProbability p) ^ 2 ≤ 2 * (1 - (p : ℝ)) at hv
  nlinarith [census_initial_sq_le_one p i]

theorem census_second_moment_sup_le_two (p : unitInterval) (hp : 99 / 100 < (p : ℝ))
    (i : Bool) : (⨆ h : ℕ, ∫ ω, censusMartingale p i h ω ^ 2 ∂broadcastMeasure p) ≤ 2 := by
  exact ciSup_le (census_second_moment_le_two p hp i)

end SphericalTreeFailures
