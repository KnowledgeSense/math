import SphericalTreeFailures.IndependenceNumber
import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace SphericalTreeFailures
open Polynomial

/-- Weight of independent sets avoiding the root. -/
noncomputable def excludedPartition (m n : ℕ) (activity : ℝ) : ℝ :=
  ((sphericalTree m n).polynomials.2).eval₂ (Nat.castRingHom ℝ) activity

/-- Total hard-core partition function of the actual tree. -/
noncomputable def totalPartition (m n : ℕ) (activity : ℝ) : ℝ :=
  (independencePolynomial (sphericalTree m n).graph Finset.univ).eval₂
    (Nat.castRingHom ℝ) activity

noncomputable def includedPartition (m n : ℕ) (activity : ℝ) : ℝ :=
  totalPartition m n activity - excludedPartition m n activity

theorem excludedPartition_succ (m n : ℕ) (activity : ℝ) :
    excludedPartition (m + 1) n activity = (totalPartition m n activity) ^ 2 := by
  simp [excludedPartition, totalPartition, ForestExpr.graph_polynomial, sphericalTree,
    ForestExpr.polynomials, pow_two]

theorem totalPartition_succ (m n : ℕ) (activity : ℝ) :
    totalPartition (m + 1) n activity =
      totalPartition m n activity ^ 2 + activity * excludedPartition m n activity ^ 2 := by
  simp only [totalPartition, ForestExpr.graph_polynomial]
  simp [excludedPartition, sphericalTree, ForestExpr.polynomials, pow_two]

theorem includedPartition_succ (m n : ℕ) (activity : ℝ) :
    includedPartition (m + 1) n activity = activity * excludedPartition m n activity ^ 2 := by
  rw [includedPartition, totalPartition_succ, excludedPartition_succ]
  ring

/-- The path tuning relation is preserved at every depth of the binary core. -/
theorem tuned_partition_ratio (n : ℕ) (activity r : ℝ)
    (hactivity : activity = r * (1 + r) ^ 2)
    (hbase : includedPartition 0 n activity = r * excludedPartition 0 n activity)
    (m : ℕ) : includedPartition m n activity = r * excludedPartition m n activity := by
  induction m with
  | zero => exact hbase
  | succ m ih =>
    have ht : totalPartition m n activity = (1 + r) * excludedPartition m n activity := by
      unfold includedPartition at ih
      linarith
    rw [includedPartition_succ, excludedPartition_succ, ht, hactivity]
    ring

end SphericalTreeFailures
