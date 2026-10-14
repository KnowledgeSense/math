import Mathlib.Data.Nat.Init

namespace ArithmeticSections

/-- The polynomial threshold in Section 4 of the release paper. -/
def tailThreshold (j : ℕ) : ℕ := ((j + 4) ^ 2 + 2) ^ 4

/-- Denominators of `[0; b₁, b₂, …]`, with the paper's indexing. -/
def denominator (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => b 1
  | n + 2 => b (n + 2) * denominator b (n + 1) + denominator b n

end ArithmeticSections
