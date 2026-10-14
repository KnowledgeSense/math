import TerminalLogConcavity.BlockSum
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace TerminalLogConcavity

/-- The exact logarithmic parameter in the release's main theorem. -/
noncomputable def logarithmicParameter (H : ℕ) : ℕ :=
  ⌈Real.logb 2 (H + 1 : ℕ)⌉₊

theorem logarithmicParameter_eq_clog (H : ℕ) :
    logarithmicParameter H = Nat.clog 2 (H + 1) := by
  simpa [logarithmicParameter] using Real.natCeil_logb_natCast 2 (H + 1)

theorem le_two_pow_logarithmicParameter (H : ℕ) : H ≤ 2 ^ logarithmicParameter H := by
  rw [logarithmicParameter_eq_clog]
  exact (Nat.le_succ H).trans (Nat.le_pow_clog (by decide) (H + 1))

theorem exact_release_order_bound {q H N : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H)
    (hcount : N + 7 * q ^ 2 + 2 =
      4 * 2 ^ thresholdIndex (target q H) * blockParameterSum q + 4 * q) :
    N ≤ 1200 * q ^ 4 * (q + logarithmicParameter H) :=
  order_bound_from_count_identity hq hH (le_two_pow_logarithmicParameter H) hcount

end TerminalLogConcavity
