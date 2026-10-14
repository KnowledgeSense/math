import MainTheorems.EulerianPencil.RootCounts
import Mathlib.Analysis.Analytic.IteratedFDeriv

namespace ResearchMain.EulerianPencil

open scoped Topology ContDiff

theorem eulerNumber_generating_function :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasSum (fun n : ℕ => eulerNumber n / (n.factorial : ℝ) * t ^ n)
        (1 / Real.cos t + Real.tan t) := by
  have hs : AnalyticAt ℝ (fun x : ℝ => 1 / Real.cos x) 0 :=
    analyticAt_const.div Real.analyticAt_cos (by simp)
  have ht : AnalyticAt ℝ Real.tan 0 := by
    exact (show ContDiffAt ℝ ω Real.tan 0 from Real.contDiffAt_tan.mpr (by simp)).analyticAt
  obtain ⟨p, hp⟩ := hs.add ht
  obtain ⟨r, hpr⟩ := hp
  have hc (n : ℕ) : p.coeff n = eulerNumber n / (n.factorial : ℝ) := by
    have he := hpr.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin n => 1)
    have he' : eulerNumber n = (n.factorial : ℝ) * p.coeff n := by
      convert! he using 1; simp only [FormalMultilinearSeries.coeff,
        Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul, Pi.one_def]
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    apply (eq_div_iff hn).mpr
    linarith
  have hps : HasFPowerSeriesAt (fun x : ℝ => 1 / Real.cos x + Real.tan x) p 0 := ⟨r, hpr⟩
  have he := hasFPowerSeriesAt_iff.mp hps
  filter_upwards [he] with t ht
  simpa only [hc, smul_eq_mul, zero_add, mul_comm (t ^ _)] using ht

end ResearchMain.EulerianPencil
