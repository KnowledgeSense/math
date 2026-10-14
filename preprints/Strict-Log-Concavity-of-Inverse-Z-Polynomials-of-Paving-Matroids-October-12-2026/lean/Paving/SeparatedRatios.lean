import Paving.Mixtures

noncomputable section
namespace Paving

/-- Common lower bound for consecutive normalized component ratios. -/
def lowerRatio (k n i : ℝ) : ℝ := (k-1-i)*(n-i+1)/(i*(n-i-1))
/-- Common upper bound for consecutive normalized component ratios. -/
def upperRatio (k n i : ℝ) : ℝ := (k-i)*(n-i+1)/(i*(n-i))

theorem ratio_bounds_order {k n i : ℝ} (hkn : k ≤ n) (hi : 0 < i) (hin : i+1 < n) :
    lowerRatio k n i ≤ upperRatio k n i := by
  have hn0 : 0 < n-i := by linarith
  have hn1 : 0 < n-i-1 := by linarith
  unfold lowerRatio upperRatio
  apply (div_le_div_iff₀ (mul_pos hi hn1) (mul_pos hi hn0)).mpr
  have hp : 0 ≤ i*(n-i+1)*(n-k) := by positivity
  nlinarith [hp]

theorem ratio_intervals_separated {k n i : ℝ}
    (hi : 0 < i) (hik : i+1 < k) (hin : i+1 < n) :
    upperRatio k n (i+1) < lowerRatio k n i := by
  have hn1 : 0 < n-i-1 := by linarith
  have hi1 : 0 < i+1 := by linarith
  unfold lowerRatio upperRatio
  apply (div_lt_div_iff₀ (mul_pos hi1 (by linarith)) (mul_pos hi hn1)).mpr
  have hp : 0 < (k-i-1)*(n-i-1)*(n+1) := by
    have hk0 : 0 < k-i-1 := by linarith
    have hn0 : 0 < n+1 := by linarith
    positivity
  nlinarith [hp]

theorem odd_middle_lowerRatio {m n : ℝ} (hm : 0 < m) (hn : m+1 < n) :
    1 < lowerRatio (2*m+1) n m := by
  have hd : 0 < m*(n-m-1) := mul_pos hm (by linarith)
  unfold lowerRatio
  apply (lt_div_iff₀ hd).mpr
  nlinarith

/-- The nonuniform component ratio, before reflection at the middle. -/
def hyperplaneRatio (k n h i : ℝ) : ℝ :=
  (k-1-i)*(n-i+1)*(h-i+1)/(i*(n-i)*(h-i))

theorem hyperplaneRatio_bounds {k n h i : ℝ}
    (hi : 0 < i) (hik : i+1 < k) (hkh : k ≤ h) (hhn : h ≤ n-1) :
    lowerRatio k n i ≤ hyperplaneRatio k n h i ∧
      hyperplaneRatio k n h i < upperRatio k n i := by
  have hh0 : 0 < h-i := by linarith
  have hn0 : 0 < n-i := by linarith
  have hn1 : 0 < n-i-1 := by linarith
  have hk0 : 0 < k-1-i := by linarith
  have hn2 : 0 < n-i+1 := by linarith
  constructor
  · unfold lowerRatio hyperplaneRatio
    apply (div_le_div_iff₀ (mul_pos hi hn1) (mul_pos (mul_pos hi hn0) hh0)).mpr
    have hdiff : 0 ≤ n-h-1 := by linarith
    have hp : 0 ≤ i*(k-1-i)*(n-i+1)*(n-h-1) := by positivity
    nlinarith [hp]
  · unfold upperRatio hyperplaneRatio
    apply (div_lt_div_iff₀ (mul_pos (mul_pos hi hn0) hh0) (mul_pos hi hn0)).mpr
    have hp : 0 < i*(n-i)*(n-i+1)*(h-k+1) := by
      have hhk : 0 < h-k+1 := by linarith
      positivity
    nlinarith [hp]

end Paving
