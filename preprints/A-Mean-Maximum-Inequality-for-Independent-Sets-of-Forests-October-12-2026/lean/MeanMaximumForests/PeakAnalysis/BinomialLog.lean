import MeanMaximumForests.PeakAnalysis.BinomialMass
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MeanMaximumForests.PeakAnalysis
open Finset

theorem log_difference_scaled (a b d : ℝ) (hd : 0 < d) (hda : d ≤ a) (hdb : d ≤ b) :
    d * |Real.log a - Real.log b| ≤ |a - b| := by
  have ha : 0 < a := hd.trans_le hda
  have hb : 0 < b := hd.trans_le hdb
  have hup (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) (hdx : d ≤ x) :
      d * (Real.log y - Real.log x) ≤ y - x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
    rw [Real.log_div hy.ne' hx.ne'] at h
    have hm := mul_le_mul_of_nonneg_left h hx.le
    have he : x * (y / x - 1) = y - x := by field_simp
    rw [he] at hm
    have hlog : 0 ≤ Real.log y - Real.log x := sub_nonneg.mpr (Real.log_le_log hx hxy)
    exact (mul_le_mul_of_nonneg_right hdx hlog).trans hm
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha hab)),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    have h := hup a b ha hb hab hda
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb hba)),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hup b a hb ha hba hdb

theorem binomial_log_step (n k : ℕ) (z : ℝ) (hz : 0 < z) (hk : k < n) :
    Real.log (binomialSizeMass n z (k + 1)) - Real.log (binomialSizeMass n z k) =
      Real.log (z * ((n : ℝ) - k)) - Real.log (k + 1 : ℝ) := by
  have hs := binomialSizeMass_step n k z
  rw [Nat.cast_sub hk.le] at hs
  have hnext := binomialSizeMass_pos n (k + 1) z hz hk
  have hprev := binomialSizeMass_pos n k z hz hk.le
  have hkpos : (0 : ℝ) < k + 1 := by positivity
  have ha : 0 < z * ((n : ℝ) - k) := mul_pos hz (sub_pos.mpr (Nat.cast_lt.mpr hk))
  have he := congrArg Real.log hs
  rw [Real.log_mul hkpos.ne' hnext.ne', Real.log_mul ha.ne' hprev.ne'] at he
  linarith only [he]

theorem binomial_log_step_scaled (n k : ℕ) (z d : ℝ) (hz : 0 < z) (hk : k < n)
    (hd : 0 < d) (hdk : d ≤ k + 1) (hdn : d ≤ z * ((n : ℝ) - k)) :
    d * |Real.log (binomialSizeMass n z (k + 1)) - Real.log (binomialSizeMass n z k)| ≤
      |z * ((n : ℝ) - k) - (k + 1)| := by
  rw [binomial_log_step n k z hz hk]
  exact log_difference_scaled _ _ d hd hdn hdk

end MeanMaximumForests.PeakAnalysis
