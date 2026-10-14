import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

namespace ResearchMain.Corona

noncomputable def logScale (t : ℝ) : ℝ := (1 + t) * Real.log (1 + t) / t

theorem logScale_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt logScale ((t - Real.log (1 + t)) / t ^ 2) t := by
  have hplus : HasDerivAt (fun s : ℝ => 1 + s) 1 t := (hasDerivAt_id t).const_add 1
  have hlog := (Real.hasDerivAt_log (by linarith : 1 + t ≠ 0)).comp t hplus
  have h := (hplus.mul hlog).div (hasDerivAt_id t) (ne_of_gt ht)
  convert h using 1
  · rfl
  · dsimp only [Function.comp_apply, Pi.mul_apply, id_eq]
    have hne : 1 + t ≠ 0 := by linarith
    field_simp
    ring

theorem logScale_strictMono : StrictMonoOn logScale (Set.Ioi (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro t ht
    exact (logScale_hasDerivAt ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 0 < t := (interior_subset ht : t ∈ Set.Ioi (0 : ℝ))
    rw [(logScale_hasDerivAt ht').deriv]
    apply div_pos
    · have h := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1 + t) (by linarith : 1 + t ≠ 1)
      linarith
    · positivity

theorem balance_separation {q : ℝ} (hq : 0 < q) :
    0 < Real.log (1 + 2 / q) / Real.log (1 + 1 / q) / (q + 1) - 2 / (q + 2) := by
  have ht₁ : (0 : ℝ) < 1 / q := by positivity
  have ht₂ : (0 : ℝ) < 2 / q := by positivity
  have hlt : (1 : ℝ) / q < 2 / q := by exact (div_lt_div_iff_of_pos_right hq).mpr (by norm_num)
  have h := logScale_strictMono ht₁ ht₂ hlt
  unfold logScale at h
  have hlu : 0 < Real.log (1 + 1 / q) := Real.log_pos (by linarith)
  have hq1 : 0 < q + 1 := by linarith
  have hq2 : 0 < q + 2 := by linarith
  have hlog : 2 * (q + 1) * Real.log (1 + 1 / q) < (q + 2) * Real.log (1 + 2 / q) := by
    field_simp at h
    have he₁ : (q + 1) / q = 1 + 1 / q := by field_simp
    have he₂ : (q + 2) / q = 1 + 2 / q := by field_simp
    rw [he₁, he₂] at h
    nlinarith
  apply sub_pos.mpr
  rw [div_div, div_lt_div_iff₀ hq2 (mul_pos hlu hq1)]
  nlinarith only [hlog]

end ResearchMain.Corona
