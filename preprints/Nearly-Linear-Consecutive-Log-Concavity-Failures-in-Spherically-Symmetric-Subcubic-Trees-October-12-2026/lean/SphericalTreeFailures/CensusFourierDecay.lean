import SphericalTreeFailures.CensusCharacteristic
import SphericalTreeFailures.CharacteristicNondegeneracy
import SphericalTreeFailures.FourierScale
import SphericalTreeFailures.ExponentialContraction

/-! # Fourier envelope iteration for the census limit -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

theorem censusEnvelope_iterate (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (n : ℕ) (t : ℝ) :
    censusEnvelope p t ≤ censusEnvelope p (t / censusScale p ^ n) ^ (2 ^ n) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    calc
      censusEnvelope p t ≤ censusEnvelope p (t / censusScale p) ^ 2 := censusEnvelope_square p hc t
      _ ≤ (censusEnvelope p ((t / censusScale p) / censusScale p ^ n) ^ (2 ^ n)) ^ 2 :=
        pow_le_pow_left₀ (censusEnvelope_nonneg p _) (ih _) 2
      _ = _ := by rw [← pow_mul, pow_succ, pow_succ, div_div, mul_comm (censusScale p)]

theorem censusEnvelope_eq_one_forces_zero (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (t : ℝ) (h : censusEnvelope p t = 1) :
    ‖censusCharacteristic p false (t / censusScale p)‖ = 1 := by
  have h0 := censusCharacteristic_norm_le_one p false (t / censusScale p)
  have h1 := censusCharacteristic_norm_le_one p true (t / censusScale p)
  have hn0 := norm_nonneg (censusCharacteristic p false (t / censusScale p))
  have hn1 := norm_nonneg (censusCharacteristic p true (t / censusScale p))
  have he : ‖censusCharacteristic p false t‖ = 1 ∨ ‖censusCharacteristic p true t‖ = 1 := by
    exact (max_eq_iff.mp h).imp And.left And.left
  rcases he with he | he
  · rw [censusCharacteristic_fixedPoint p hc false, norm_pow] at he
    change ‖censusMixtureCharacteristic p (-t / censusScale p)‖ ^ 2 = 1 at he
    have hn := norm_nonneg (censusMixtureCharacteristic p (-t / censusScale p))
    have he' : ‖censusMixtureCharacteristic p (-t / censusScale p)‖ = 1 := by nlinarith
    have hb : ‖censusMixtureCharacteristic p (-t / censusScale p)‖ ≤
        (1 - (p : ℝ)) * ‖censusCharacteristic p false (t / censusScale p)‖ +
        (p : ℝ) * ‖censusCharacteristic p true (t / censusScale p)‖ := by
      rw [censusMixtureCharacteristic_eq]
      convert norm_add_le
        (((1 - (p : ℝ) : ℝ) : ℂ) * censusCharacteristic p false (-t / censusScale p))
        ((p : ℂ) * censusCharacteristic p true (-t / censusScale p)) using 1
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr p.property.2), abs_of_nonneg p.property.1,
        neg_div, censusCharacteristic_norm_neg]
    rw [he'] at hb
    have hh := mul_le_mul_of_nonneg_left h1 p.property.1
    nlinarith
  · rw [censusCharacteristic_fixedPoint_one p hc, norm_pow, neg_div,
      censusCharacteristic_norm_neg] at he
    nlinarith

theorem censusEnvelope_eq_one_scaled (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) (t : ℝ) (h : censusEnvelope p t = 1) (n : ℕ) :
    censusEnvelope p (t / censusScale p ^ n) = 1 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply le_antisymm (censusEnvelope_le_one p _)
    have hzero := censusEnvelope_eq_one_forces_zero p hc hp1 (t / censusScale p ^ n) ih
    have he : (t / censusScale p ^ n) / censusScale p = t / censusScale p ^ (n + 1) := by
      rw [div_div, pow_succ]
    rw [he] at hzero
    exact hzero ▸ le_max_left _ _

theorem censusScale_gt_one (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) :
    1 < censusScale p := by
  unfold censusScale
  nlinarith [p.property.1, p.property.2]

theorem censusCharacteristic_lt_one_near_zero (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (hp1 : (p : ℝ) < 1) (i : Bool) :
    ∀ᶠ t : ℝ in 𝓝 0, t ≠ 0 → ‖censusCharacteristic p i t‖ < 1 := by
  apply charFun_lt_one_near_zero
  · exact (memLp_map_measure_iff (by fun_prop) (measurable_censusLimit p i).aemeasurable).mpr
      (memLp_censusLimit p i)
  · unfold censusLimitLaw
    rw [variance_id_map (measurable_censusLimit p i).aemeasurable]
    exact variance_censusLimit_pos p hc hp1 i

/-- No nonzero lattice frequency survives the actual broadcast fixed point. -/
theorem censusEnvelope_lt_one (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) {t : ℝ} (ht : t ≠ 0) : censusEnvelope p t < 1 := by
  apply lt_of_le_of_ne (censusEnvelope_le_one p t)
  intro he
  have hg := censusScale_gt_one p hc
  have hscale : Tendsto (fun n : ℕ => t / censusScale p ^ n) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := t)).mul
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hg))
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_apply] using hh
  have h0 := hscale.eventually (censusCharacteristic_lt_one_near_zero p hc hp1 false)
  have h1 := hscale.eventually (censusCharacteristic_lt_one_near_zero p hc hp1 true)
  obtain ⟨n, hn0, hn1⟩ := (h0.and h1).exists
  have hn : t / censusScale p ^ n ≠ 0 := div_ne_zero ht (pow_ne_zero _ (by linarith))
  have hlt : censusEnvelope p (t / censusScale p ^ n) < 1 := max_lt (hn0 hn) (hn1 hn)
  rw [censusEnvelope_eq_one_scaled p hc hp1 t he n] at hlt
  exact lt_irrefl _ hlt

theorem censusCharacteristic_continuous (p : unitInterval) (i : Bool) :
    Continuous (censusCharacteristic p i) := continuous_charFun

theorem censusEnvelope_continuous (p : unitInterval) : Continuous (censusEnvelope p) :=
  (censusCharacteristic_continuous p false).norm.max (censusCharacteristic_continuous p true).norm

theorem censusEnvelope_abs (p : unitInterval) (t : ℝ) : censusEnvelope p |t| = censusEnvelope p t := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg ht, censusEnvelope_neg]

theorem censusEnvelope_annulus_bound (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (hp1 : (p : ℝ) < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ t : ℝ, 1 ≤ |t| → |t| ≤ censusScale p →
      censusEnvelope p t ≤ ρ := by
  have hg := censusScale_gt_one p hc
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc 1 (censusScale p)).Nonempty from ⟨1, le_rfl, hg.le⟩)
    (censusEnvelope_continuous p).continuousOn
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hlt := censusEnvelope_lt_one p hc hp1 hx0
  refine ⟨(censusEnvelope p x + 1) / 2, ?_, ?_, ?_⟩
  · linarith [censusEnvelope_nonneg p x]
  · linarith
  · intro t ht1 htγ
    have hb : censusEnvelope p |t| ≤ censusEnvelope p x := hmax ⟨ht1, htγ⟩
    rw [censusEnvelope_abs] at hb
    linarith

/-- Stretched exponential decay with the exact release exponent. -/
theorem censusEnvelope_stretched_exponential (p : unitInterval)
    (hc : 1 < 2 * (p : ℝ) ^ 2) (hp1 : (p : ℝ) < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ,
      censusEnvelope p t ≤ C * Real.exp (-c * |t| ^ fourierExponent (censusScale p)) := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := censusEnvelope_annulus_bound p hc hp1
  have hg := censusScale_gt_one p hc
  let c : ℝ := -Real.log ρ / 2
  have hc0 : 0 < c := contraction_constant_pos hρ0 hρ1 (by norm_num)
  refine ⟨c, Real.exp c, hc0, Real.exp_pos _, ?_⟩
  intro t
  by_cases ht : 1 ≤ |t|
  · obtain ⟨n, _, _, hn0, hn1, hnpow⟩ := exists_fourier_annulus hg ht
    have hi := censusEnvelope_iterate p hc n t
    have hb := hρ (t / censusScale p ^ n) hn0 hn1
    have hd : censusEnvelope p t ≤ Real.exp (-c * |t| ^ fourierExponent (censusScale p)) := by
      apply (hi.trans (pow_le_pow_left₀ (censusEnvelope_nonneg p _) hb _)).trans
      exact power_contraction_bound hρ0 hρ1 (by norm_num : (0 : ℝ) < 2) (2 ^ n)
        (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnpow)
    exact hd.trans (le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_exp hc0.le))
  · exact (censusEnvelope_le_one p t).trans
      (small_frequency_exponential_bound hc0.le (fourierExponent_pos hg).le (by linarith))

end SphericalTreeFailures
