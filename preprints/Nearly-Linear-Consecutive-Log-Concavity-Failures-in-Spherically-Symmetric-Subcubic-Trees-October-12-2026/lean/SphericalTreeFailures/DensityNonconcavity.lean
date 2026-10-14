import SphericalTreeFailures.DensityConcentration

/-! # A quantitative obstruction to log-concavity for the actual root mixture -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem separated_peak_numerics {ε p : ℝ} (he : 0 < ε) (he' : ε < 1 / 8192)
    (hp : 99 / 100 < p) :
    (114 * ε) ^ 8 < ((63 / 16) * ε) ^ 5 * ((63 / 16) * p) ^ 3 := by
  have hε : ε ^ 3 ≤ (1 / 8192 : ℝ) ^ 3 := pow_le_pow_left₀ he.le he'.le 3
  have hp' : (99 / 100 : ℝ) ^ 3 ≤ p ^ 3 := pow_le_pow_left₀ (by norm_num) hp.le 3
  have h : (114 : ℝ) ^ 8 * ε ^ 3 < (63 / 16 : ℝ) ^ 8 * p ^ 3 := calc
    _ ≤ (114 : ℝ) ^ 8 * (1 / 8192 : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hε (by norm_num)
    _ < (63 / 16 : ℝ) ^ 8 * (99 / 100 : ℝ) ^ 3 := by norm_num
    _ ≤ (63 / 16 : ℝ) ^ 8 * p ^ 3 := mul_le_mul_of_nonneg_left hp' (by norm_num)
  have hh := mul_lt_mul_of_pos_left h (pow_pos he 5)
  nlinarith only [hh]

theorem concave_log_power_bound {f : ℝ → ℝ} (hf : ∀ x, 0 < f x)
    (hc : ConcaveOn ℝ Set.univ (fun x => Real.log (f x))) (a b : ℝ) :
    (f a) ^ 5 * (f b) ^ 3 ≤ (f ((5 * a + 3 * b) / 8)) ^ 8 := by
  have h := hc.2 (Set.mem_univ a) (Set.mem_univ b)
    (show (0 : ℝ) ≤ 5 / 8 by norm_num) (show (0 : ℝ) ≤ 3 / 8 by norm_num)
    (show (5 / 8 : ℝ) + 3 / 8 = 1 by norm_num)
  simp only [smul_eq_mul] at h
  have he : 5 / 8 * a + 3 / 8 * b = (5 * a + 3 * b) / 8 := by ring
  rw [he] at h
  apply (Real.log_le_log_iff (mul_pos (pow_pos (hf a) 5) (pow_pos (hf b) 3))
    (pow_pos (hf _) 8)).mp
  rw [Real.log_mul (ne_of_gt (pow_pos (hf a) 5)) (ne_of_gt (pow_pos (hf b) 3)),
    Real.log_pow, Real.log_pow, Real.log_pow]
  norm_num
  linarith

theorem concave_log_min_interval {f : ℝ → ℝ} (hf : ∀ x, 0 < f x)
    (hc : ConcaveOn ℝ Set.univ (fun x => Real.log (f x)))
    {a b M : ℝ} (hab : a < b) (hM : 0 < M) (ha : M ≤ f a) (hb : M ≤ f b)
    {x : ℝ} (hx : x ∈ Set.Icc a b) : M ≤ f x := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have h1 : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hx.2) hba.le
  have h2 : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) hba.le
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp
    ring
  have he : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp
    ring
  have h := hc.2 (Set.mem_univ a) (Set.mem_univ b) h1 h2 hsum
  simp only [smul_eq_mul, he] at h
  apply (Real.log_le_log_iff hM (hf x)).mp
  calc
    Real.log M = ((b - x) / (b - a) + (x - a) / (b - a)) * Real.log M := by rw [hsum, one_mul]
    _ ≤ (b - x) / (b - a) * Real.log (f a) + (x - a) / (b - a) * Real.log (f b) := by
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (Real.log_le_log hM ha) h1)
        (mul_le_mul_of_nonneg_left (Real.log_le_log hM hb) h2)
    _ ≤ Real.log (f x) := h

theorem separated_peaks_not_log_concave {f : ℝ → ℝ} (hf : ∀ x, 0 < f x)
    (hfi : Integrable f) {ε p μ a b : ℝ}
    (he : 0 < ε) (he' : ε < 1 / 8192) (hp : 99 / 100 < p)
    (ha : a ∈ Set.Icc (μ - 1 / 8) (μ + 1 / 8))
    (hb : b ∈ Set.Icc (μ + 7 / 8) (μ + 9 / 8))
    (hfa : (63 / 16) * ε ≤ f a) (hfb : (63 / 16) * p ≤ f b)
    (hmass : (∫ x in Set.Icc (μ + 1 / 2) (μ + 5 / 8), f x) ≤ 128 * ε / 9) :
    ¬ ConcaveOn ℝ Set.univ (fun x => Real.log (f x)) := by
  intro hc
  let z := (5 * a + 3 * b) / 8
  have hz : 114 * ε < f z := by
    have ht := (separated_peak_numerics he he' hp).trans_le
      ((mul_le_mul (pow_le_pow_left₀ (by positivity) hfa 5)
        (pow_le_pow_left₀ (by positivity) hfb 3) (by positivity)
        (pow_nonneg (hf a).le 5)).trans (concave_log_power_bound hf hc a b))
    exact (pow_lt_pow_iff_left₀ (by positivity) (hf z).le (by decide : 8 ≠ 0)).mp ht
  have hb' : 114 * ε ≤ f b := by
    have : 114 * ε < (63 / 16) * p := by linarith
    exact this.le.trans hfb
  have hzb : z < b := by dsimp [z]; rcases ha with ⟨ha1,ha2⟩; rcases hb with ⟨hb1,hb2⟩; linarith
  have hlow : 114 * ε / 8 ≤ ∫ x in Set.Icc (μ + 1 / 2) (μ + 5 / 8), f x := by
    calc
      _ = ∫ _ in Set.Icc (μ + 1 / 2) (μ + 5 / 8), 114 * ε := by
        rw [setIntegral_const, Real.volume_real_Icc]
        have : μ + 5 / 8 - (μ + 1 / 2) = (1 / 8 : ℝ) := by ring
        rw [this, max_eq_left (by norm_num)]
        simp only [smul_eq_mul]
        ring
      _ ≤ _ := setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Icc]))
        hfi.integrableOn measurableSet_Icc (fun x hx =>
          concave_log_min_interval hf hc hzb (by positivity) hz.le hb' (by
            dsimp [z]; rcases ha with ⟨ha1,ha2⟩; rcases hb with ⟨hb1,hb2⟩
            constructor <;> linarith [hx.1, hx.2]))
  linarith

theorem censusMixtureDensity_integrable (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) : Integrable (censusMixtureDensity p) :=
  ((censusDensity_integrable p hc hp1 false).const_mul (1 - (p : ℝ))).add
    ((censusDensity_integrable p hc hp1 true).const_mul (p : ℝ))

theorem censusDensity_peak (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp : 99 / 100 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (he : 1 - (p : ℝ) < 1 / 8192) (i : Bool) :
    ∃ x ∈ Set.Icc (boolIndicator i - stationaryProbability p - 1 / 8)
      (boolIndicator i - stationaryProbability p + 1 / 8), 63 / 16 ≤ censusDensity p i x := by
  have hm := censusDensity_interval_mass p hc hp hp1 i (r := 1 / 8) (by norm_num)
  have hm' : 63 / 64 ≤ ∫ x in Set.Icc
      (boolIndicator i - stationaryProbability p - 1 / 8)
      (boolIndicator i - stationaryProbability p + 1 / 8), censusDensity p i x := by
    norm_num at hm
    linarith
  obtain ⟨x,hx,hh⟩ := interval_density_peak (censusDensity_continuous p hc hp1 i)
    (censusDensity_integrable p hc hp1 i) (by linarith) hm'
  exact ⟨x,hx,by linarith⟩

theorem censusDensity_middle_mass (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp : 99 / 100 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (i : Bool) :
    (∫ x in Set.Icc (-stationaryProbability p + 1 / 2)
      (-stationaryProbability p + 5 / 8), censusDensity p i x) ≤ 128 * (1 - (p : ℝ)) / 9 := by
  rw [← density_measureReal_eq_integral _ (censusDensity_continuous p hc hp1 i).measurable
    (censusDensity_nonneg p hc hp1 i) (censusLimitLaw_eq_withDensity p hc hp1 i) measurableSet_Icc]
  have ht := censusLimitLaw_chebyshev p hc hp i (r := 3 / 8) (by norm_num)
  have hs : Set.Icc (-stationaryProbability p + 1 / 2)
      (-stationaryProbability p + 5 / 8) ⊆
      {x | 3 / 8 ≤ |x - (boolIndicator i - stationaryProbability p)|} := by
    intro x hx
    cases i
    · simp only [boolIndicator, Bool.false_eq_true, ↓reduceIte, zero_sub]
      exact le_trans (by linarith [hx.1] : (3 : ℝ) / 8 ≤ x - -stationaryProbability p)
        (le_abs_self _)
    · simp only [boolIndicator, ↓reduceIte]
      exact le_trans (by linarith [hx.2] : (3 : ℝ) / 8 ≤ -(x - (1 - stationaryProbability p)))
        (neg_le_abs _)
  have hb := (measureReal_mono (μ := censusLimitLaw p i) hs).trans ht
  convert hb using 1; ring

theorem censusMixtureDensity_middle_mass (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp : 99 / 100 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (∫ x in Set.Icc (-stationaryProbability p + 1 / 2)
      (-stationaryProbability p + 5 / 8), censusMixtureDensity p x) ≤ 128 * (1 - (p : ℝ)) / 9 := by
  unfold censusMixtureDensity
  rw [integral_add ((censusDensity_integrable p hc hp1 false).integrableOn.const_mul (1 - (p : ℝ)))
    ((censusDensity_integrable p hc hp1 true).integrableOn.const_mul (p : ℝ)),
    integral_const_mul, integral_const_mul]
  have h0 := mul_le_mul_of_nonneg_left (censusDensity_middle_mass p hc hp hp1 false)
    (sub_nonneg.mpr p.property.2)
  have h1 := mul_le_mul_of_nonneg_left (censusDensity_middle_mass p hc hp hp1 true) p.property.1
  nlinarith only [add_le_add h0 h1]

theorem censusMixtureDensity_not_log_concave (p : unitInterval)
    (hp : 99 / 100 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (he : 1 - (p : ℝ) < 1 / 8192) :
    ¬ ConcaveOn ℝ Set.univ (fun x => Real.log (censusMixtureDensity p x)) := by
  have hc : 1 < 2 * (p : ℝ) ^ 2 := by nlinarith
  obtain ⟨a,ha,hfa⟩ := censusDensity_peak p hc hp hp1 he false
  obtain ⟨b,hb,hfb⟩ := censusDensity_peak p hc hp hp1 he true
  apply separated_peaks_not_log_concave (censusMixtureDensity_pos p hc hp1)
    (censusMixtureDensity_integrable p hc hp1) (sub_pos.mpr hp1) he hp
    (μ := -stationaryProbability p) (a := a) (b := b)
  · simpa only [boolIndicator, Bool.false_eq_true, ↓reduceIte, zero_sub] using ha
  · simp only [boolIndicator, ↓reduceIte] at hb
    constructor <;> linarith [hb.1, hb.2]
  · unfold censusMixtureDensity
    have h := mul_le_mul_of_nonneg_left hfa (sub_nonneg.mpr p.property.2)
    have hn := mul_nonneg p.property.1 (censusDensity_nonneg p hc hp1 true a)
    nlinarith only [h, hn]
  · unfold censusMixtureDensity
    have h := mul_le_mul_of_nonneg_left hfb p.property.1
    have hn := mul_nonneg (sub_nonneg.mpr p.property.2) (censusDensity_nonneg p hc hp1 false b)
    nlinarith only [h, hn]
  · exact censusMixtureDensity_middle_mass p hc hp hp1

end SphericalTreeFailures
