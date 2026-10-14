import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
namespace AperyMoments
open Filter Set
open scoped Topology NNReal ENNReal

theorem scalar_powerSeries_coeff_unique {a b : ℕ→ℝ} {r : ℝ} (hr : 0<r)
    (ha : Summable (fun n=>a n*r^n)) (hb : Summable (fun n=>b n*r^n))
    (he : ∀ t:ℝ, 0<t → t<r → (∑' n,a n*t^n)=(∑' n,b n*t^n)) : a=b := by
  let p := FormalMultilinearSeries.ofScalars ℝ a
  let q := FormalMultilinearSeries.ofScalars ℝ b
  let ρ : ℝ≥0 := ⟨r,hr.le⟩
  have hp : (ρ:ℝ≥0∞)≤p.radius := by
    apply FormalMultilinearSeries.le_radius_of_summable
    change Summable (fun n=>‖p n‖*r^n)
    simpa only [p,FormalMultilinearSeries.ofScalars_norm,norm_mul,norm_pow,
      Real.norm_eq_abs,abs_of_pos hr] using ha.norm
  have hq : (ρ:ℝ≥0∞)≤q.radius := by
    apply FormalMultilinearSeries.le_radius_of_summable
    change Summable (fun n=>‖q n‖*r^n)
    simpa only [q,FormalMultilinearSeries.ofScalars_norm,norm_mul,norm_pow,
      Real.norm_eq_abs,abs_of_pos hr] using hb.norm
  have hρ : (0:ℝ≥0∞)<ρ := by exact_mod_cast hr
  have hpa := (p.hasFPowerSeriesOnBall (hρ.trans_le hp)).hasFPowerSeriesAt
  have hqa := (q.hasFPowerSeriesOnBall (hρ.trans_le hq)).hasFPowerSeriesAt
  have hepos : ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ),p.sum t=q.sum t := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hr)] with t ht htr
    change FormalMultilinearSeries.ofScalarsSum a t=FormalMultilinearSeries.ofScalarsSum b t
    simpa only [FormalMultilinearSeries.ofScalars_sum_eq,smul_eq_mul] using he t ht htr
  have hefreq : ∃ᶠ t:ℝ in 𝓝[≠] (0:ℝ),p.sum t=q.sum t :=
    hepos.frequently.filter_mono (nhdsWithin_mono _ (fun t ht=>ne_of_gt ht))
  have hevent := (hpa.analyticAt.frequently_eq_iff_eventually_eq hqa.analyticAt).mp hefreq
  exact FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ
    (hpa.eq_formalMultilinearSeries_of_eventually hqa hevent)

end AperyMoments
