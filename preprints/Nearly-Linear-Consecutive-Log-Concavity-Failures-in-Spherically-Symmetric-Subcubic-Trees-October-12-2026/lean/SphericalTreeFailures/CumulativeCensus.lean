import SphericalTreeFailures.CensusFixedPoint

/-! # The cumulative core census

The signed, normalized total occupation fluctuation in the binary core converges
in L² to `γ / (1 + γ)` times the generation census limit.
-/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal ProbabilityTheory Topology

noncomputable def censusRate (p : ℝ) : ℝ := Real.sqrt ((2 * p ^ 2)⁻¹)

theorem censusRate_bounds (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) :
    0 ≤ censusRate p ∧ censusRate p < 1 := by
  constructor
  · exact Real.sqrt_nonneg _
  · apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
    simpa using (inv_lt_one₀ (by positivity : 0 < 2 * (p : ℝ) ^ 2)).mpr hc

theorem censusL2_error_geometric (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (i : Bool) (h : ℕ) :
    ‖censusL2 p i h - censusLimitL2 p i‖ ≤
      (censusRate p / (1 - censusRate p)) * censusRate p ^ h := by
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  have he := dist_le_of_le_geometric_of_tendsto (censusRate p) (censusRate p)
    (censusRate_bounds p hc).2
    (f := censusL2 p i)
    (fun n => by
      rw [dist_comm, dist_eq_norm]
      simpa only [pow_succ, mul_comm, censusRate] using censusL2_increment_bound p hp i n)
    (censusL2_tendsto p hc i) h
  simpa only [dist_eq_norm, div_mul_eq_mul_div] using he

/-- A stable affine recursion inherits a summable geometric error bound. -/
theorem affine_recursion_tendsto_of_geometric_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x u : ℕ → E) (T U : E) (a s D : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (_hD : 0 ≤ D) (ha : ‖a‖ ≤ s)
    (hrec : ∀ n, x (n + 1) = a • x n + u (n + 1))
    (hfix : a • T + U = T) (hu : ∀ n, ‖u n - U‖ ≤ D * s ^ n) :
    Tendsto x atTop (𝓝 T) := by
  have hb (n : ℕ) : ‖x n - T‖ ≤ (‖x 0 - T‖ + D * n) * s ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have he : x (n + 1) - T = a • (x n - T) + (u (n + 1) - U) := by
        rw [hrec, smul_sub]
        calc
          a • x n + u (n + 1) - T = a • x n + u (n + 1) - (a • T + U) := by rw [hfix]
          _ = _ := by abel
      rw [he]
      calc
        _ ≤ ‖a • (x n - T)‖ + ‖u (n + 1) - U‖ := norm_add_le _ _
        _ ≤ s * ((‖x 0 - T‖ + D * n) * s ^ n) + D * s ^ (n + 1) := by
          rw [norm_smul]
          exact add_le_add (mul_le_mul ha ih (norm_nonneg _) hs0) (hu (n + 1))
        _ = (‖x 0 - T‖ + D * (n + 1 : ℕ)) * s ^ (n + 1) := by
          push_cast
          rw [pow_succ]
          ring
  have hr : ‖s‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hs0] using hs1
  have hs : Summable (fun n : ℕ => (‖x 0 - T‖ + D * n) * s ^ n) := by
    have h1 := (summable_geometric_of_lt_one hs0 hs1).mul_left ‖x 0 - T‖
    have h2 := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left D
    convert h1.add h2 using 1
    funext n
    simp only [pow_one]
    ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hb hs.tendsto_atTop_zero

/-- The cumulative centered occupation, normalized by the signed generation scale. -/
noncomputable def cumulativeCensus (p : ℝ) (i : Bool) (h : ℕ) (ω : BroadcastSpace) : ℝ :=
  ((-censusScale p) ^ h)⁻¹ * ∑ l ∈ Finset.range (h + 1), census p i l ω

noncomputable def cumulativeCensusL2 (p : unitInterval) (i : Bool) : ℕ → Lp ℝ 2 (broadcastMeasure p)
  | 0 => censusL2 p i 0
  | h + 1 => (-censusScale p)⁻¹ • cumulativeCensusL2 p i h + censusL2 p i (h + 1)

theorem cumulativeCensus_succ (p : ℝ) (hp : 0 < p) (i : Bool) (h : ℕ) (ω : BroadcastSpace) :
    cumulativeCensus p i (h + 1) ω =
      (-censusScale p)⁻¹ * cumulativeCensus p i h ω + censusMartingale p i (h + 1) ω := by
  unfold cumulativeCensus censusMartingale
  rw [Finset.sum_range_succ, pow_succ]
  have hg : censusScale p ≠ 0 := by unfold censusScale; positivity
  field_simp
  ring

theorem cumulativeCensusL2_ae_eq (p : unitInterval) (hp : 0 < (p : ℝ)) (i : Bool) (h : ℕ) :
    (cumulativeCensusL2 p i h : BroadcastSpace → ℝ) =ᵐ[broadcastMeasure p] cumulativeCensus p i h := by
  induction h with
  | zero =>
    refine (memLp_censusMartingale p i 0 2).coeFn_toLp.trans (ae_of_all _ fun ω => ?_)
    simp [cumulativeCensus, censusMartingale]
  | succ h ih =>
    have hs := Lp.coeFn_smul ((-censusScale p)⁻¹) (cumulativeCensusL2 p i h)
    have ha := Lp.coeFn_add (((-censusScale p)⁻¹) • cumulativeCensusL2 p i h) (censusL2 p i (h + 1))
    filter_upwards [ha, hs, ih, (memLp_censusMartingale p i (h + 1) 2).coeFn_toLp] with ω hA hS hI hM
    change (censusL2 p i (h + 1)) ω = _ at hM
    rw [cumulativeCensusL2, hA]
    dsimp only [Pi.add_apply]
    rw [hS]
    dsimp only [Pi.smul_apply, smul_eq_mul]
    rw [hI, hM, cumulativeCensus_succ p hp i h ω]

theorem inverse_scale_le_censusRate (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) :
    ‖(-censusScale p)⁻¹‖ ≤ censusRate p := by
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  apply (sq_le_sq₀ (norm_nonneg _) (censusRate_bounds p hc).1).mp
  rw [censusRate, Real.sq_sqrt (by positivity), Real.norm_eq_abs, sq_abs]
  unfold censusScale
  field_simp
  nlinarith

theorem cumulativeCensusL2_tendsto (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    Tendsto (cumulativeCensusL2 p i) atTop
      (𝓝 ((censusScale p / (1 + censusScale p)) • censusLimitL2 p i)) := by
  obtain ⟨hs0, hs1⟩ := censusRate_bounds p hc
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  apply affine_recursion_tendsto_of_geometric_error (cumulativeCensusL2 p i) (censusL2 p i)
    _ (censusLimitL2 p i) ((-censusScale p)⁻¹) (censusRate p) (censusRate p / (1 - censusRate p))
    hs0 hs1 (div_nonneg hs0 (by linarith)) (inverse_scale_le_censusRate p hc)
  · exact fun _ => rfl
  · have hg : 0 < censusScale p := by unfold censusScale; positivity
    have he : (-censusScale p)⁻¹ * (censusScale p / (1 + censusScale p)) + 1 =
        censusScale p / (1 + censusScale p) := by field_simp; ring
    calc
      _ = ((-censusScale p)⁻¹ * (censusScale p / (1 + censusScale p)) + 1) •
          censusLimitL2 p i := by rw [add_smul, one_smul, smul_smul]
      _ = _ := by rw [he]
  · exact censusL2_error_geometric p hc i

theorem cumulativeCensus_tendsto_L2 (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    Tendsto (fun h => eLpNorm
      (cumulativeCensus p i h - (censusScale p / (1 + censusScale p)) • censusLimit p i)
      2 (broadcastMeasure p)) atTop (𝓝 0) := by
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  have ht := (cumulativeCensusL2_tendsto p hc i).edist
    (tendsto_const_nhds (x := (censusScale p / (1 + censusScale p)) • censusLimitL2 p i))
  simp only [edist_self] at ht
  apply ht.congr'
  exact Eventually.of_forall fun h => by
    dsimp only
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((cumulativeCensusL2_ae_eq p hp i h).sub
      (Lp.coeFn_smul (censusScale p / (1 + censusScale p)) (censusLimitL2 p i)))

end SphericalTreeFailures
