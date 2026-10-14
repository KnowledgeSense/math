import SphericalTreeFailures.ReleaseDensityDerivatives

namespace SphericalTreeFailures

theorem product_approximation_bound {A B a b M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hA : |A - a| ≤ ε) (hB : |B - b| ≤ ε) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |A * B - a * b| ≤ ε * (2 * M + ε) := by
  have hAB : |A| ≤ M + ε := by
    calc |A| = |a + (A - a)| := by congr 1; ring
         _ ≤ |a| + |A - a| := abs_add_le _ _
         _ ≤ M + ε := add_le_add ha hA
  calc
    |A * B - a * b| = |A * (B - b) + (A - a) * b| := by congr 1; ring
    _ ≤ |A| * |B - b| + |A - a| * |b| := by simpa only [abs_mul] using abs_add_le (A * (B - b)) ((A - a) * b)
    _ ≤ (M + ε) * ε + ε * M := add_le_add
      (mul_le_mul hAB hB (abs_nonneg _) (by positivity))
      (mul_le_mul hA hb (abs_nonneg _) hε)
    _ = ε * (2 * M + ε) := by ring

theorem curvature_approximation_bound {A B C D a b c M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hA : |A - a| ≤ ε) (hB : |B - b| ≤ ε) (hC : |C - c| ≤ ε) (hD : |D - c| ≤ ε)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M) :
    |(A * B - C * D) - (a * b - c ^ 2)| ≤ 2 * ε * (2 * M + ε) := by
  have h1 := product_approximation_bound hM hε hA hB ha hb
  have h2 := product_approximation_bound hM hε hC hD hc hc
  calc
    _ = |(A * B - a * b) - (C * D - c * c)| := by congr 1; ring
    _ ≤ |A * B - a * b| + |C * D - c * c| := abs_sub _ _
    _ ≤ ε * (2 * M + ε) + ε * (2 * M + ε) := add_le_add h1 h2
    _ = _ := by ring

theorem scaledMassDifference_curvature (H : ℝ) (w : ℤ → ℝ) (j : ℤ) :
    scaledMassDifference .value H w j * scaledMassDifference .second H w j -
      scaledMassDifference .forward H w j * scaledMassDifference .backward H w j =
        H ^ 4 * (w (j - 1) * w (j + 1) - w j ^ 2) := by
  unfold scaledMassDifference
  ring

end SphericalTreeFailures
