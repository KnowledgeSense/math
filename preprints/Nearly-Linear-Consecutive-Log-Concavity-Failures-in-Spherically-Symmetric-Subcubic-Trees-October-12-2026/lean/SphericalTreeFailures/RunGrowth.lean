import SphericalTreeFailures.RunLocation
import SphericalTreeFailures.TreeGeometry

namespace SphericalTreeFailures
open Filter
open scoped Topology

theorem normalized_vertexCard_tendsto (n : ℕ) :
    Tendsto (fun m => (Fintype.card (sphericalTree m n).Vertex : ℝ) / 2 ^ m)
      atTop (𝓝 ((n : ℝ) + 2)) := by
  have h := (tendsto_const_nhds (x := (n : ℝ) + 2)).sub inverse_two_pow_tendsto
  simp only [sub_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun m => by
    have he : (Fintype.card (sphericalTree m n).Vertex : ℝ) + 1 = (n + 2) * (2 : ℝ) ^ m := by
      exact_mod_cast sphericalTree_card m n
    dsimp only
    field_simp
    nlinarith

theorem releaseScale_exponent_dominates (k : ℕ) (hk : 16384 ≤ k) {η : ℝ}
    (hη : (2 : ℝ) ^ (-η) < (k : ℝ) / (k + 2)) :
    (2 : ℝ) ^ (1 - η) < fluctuationScale (releaseParameter k hk) := by
  have hp := (broadcastParameter_bounds hk (releaseParameter_spec k hk).1).1
  rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  unfold fluctuationScale
  linarith

theorem vertexPower_scale_tendsto (k : ℕ) (hk : 16384 ≤ k) {η : ℝ}
    (hη : (2 : ℝ) ^ (-η) < (k : ℝ) / (k + 2)) :
    Tendsto (fun m => (Fintype.card (sphericalTree m (2 * k + 1)).Vertex : ℝ) ^ (1 - η) /
      releaseScale k hk m) atTop (𝓝 0) := by
  let γ := fluctuationScale (releaseParameter k hk)
  have hγ : 0 < γ := by have := release_scale_gt_one k hk; dsimp [γ]; linarith
  have hr : (2 : ℝ) ^ (1 - η) / γ < 1 :=
    (div_lt_one hγ).mpr (releaseScale_exponent_dominates k hk hη)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (Real.rpow_nonneg (by norm_num) _) hγ.le) hr
  have hbase := (normalized_vertexCard_tendsto (2 * k + 1)).rpow_const (p := 1 - η)
    (Or.inl (by positivity : ((2 * k + 1 : ℕ) : ℝ) + 2 ≠ 0))
  have h := hbase.mul hpow
  simp only [mul_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun m => by
    dsimp only
    rw [Real.div_rpow (by positivity) (by positivity)]
    have he : ((2 : ℝ) ^ m) ^ (1 - η) = ((2 : ℝ) ^ (1 - η)) ^ m := by
      rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      ring
    rw [he, div_pow]
    unfold releaseScale
    dsimp [γ]
    field_simp

theorem releaseRun_card_growth (k : ℕ) (hk : 16384 ≤ k) {η a b : ℝ}
    (hη : (2 : ℝ) ^ (-η) < (k : ℝ) / (k + 2)) (hab : a < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m in atTop,
      C * (Fintype.card (sphericalTree m (2 * k + 1)).Vertex : ℝ) ^ (1 - η) ≤
        ((releaseRun k hk a b m).card : ℝ) := by
  refine ⟨1, by norm_num, ?_⟩
  have hH := tendsto_pow_atTop_atTop_of_one_lt (release_scale_gt_one k hk)
  have hsmall := (vertexPower_scale_tendsto k hk hη).eventually (gt_mem_nhds (by linarith : 0 < (b - a) / 2))
  have hlarge := hH.eventually (eventually_ge_atTop (2 / (b - a)))
  filter_upwards [hsmall, hlarge] with m hm hlarge
  have hp := releaseScale_pos k hk m
  have h1 : (Fintype.card (sphericalTree m (2 * k + 1)).Vertex : ℝ) ^ (1 - η) <
      (b - a) / 2 * releaseScale k hk m := (div_lt_iff₀ hp).mp hm
  have h2 : 1 ≤ (b - a) / 2 * releaseScale k hk m := by
    change 2 / (b - a) ≤ releaseScale k hk m at hlarge
    have := (div_le_iff₀ (sub_pos.mpr hab)).mp hlarge
    nlinarith
  have h3 := releaseRun_card_lower k hk a b m
  simp only [one_mul]
  nlinarith

end SphericalTreeFailures
