import SphericalTreeFailures.TunedRootProbability

namespace SphericalTreeFailures
open Polynomial

/-- Size polynomials conditioned on root absence or presence, respectively. -/
noncomputable def conditionalPolynomials : ℕ → ℕ → ℕ[X] × ℕ[X]
  | 0, k => (pathPolynomial (2 * k + 1), X * pathPolynomial (2 * k))
  | m + 1, k =>
    let p := conditionalPolynomials m k
    ((p.1 + p.2) ^ 2, X * p.1 ^ 2)

theorem conditionalPolynomials_graph (m k : ℕ) :
    (conditionalPolynomials m k).1 = (sphericalTree m (2 * k + 1)).polynomials.2 ∧
    (conditionalPolynomials m k).1 + (conditionalPolynomials m k).2 =
      (sphericalTree m (2 * k + 1)).polynomials.1 := by
  induction m with
  | zero =>
    constructor
    · rfl
    · rfl
  | succ m ih =>
    simp only [conditionalPolynomials]
    rw [ih.2, ih.1]
    simp [sphericalTree, ForestExpr.polynomials, pow_two]

theorem conditionalPolynomials_excluded (m k : ℕ) (activity : ℝ) :
    (conditionalPolynomials m k).1.eval₂ (Nat.castRingHom ℝ) activity =
      excludedPartition m (2 * k + 1) activity := by
  rw [(conditionalPolynomials_graph m k).1]
  rfl

theorem conditionalPolynomials_included (m k : ℕ) (activity : ℝ) :
    (conditionalPolynomials m k).2.eval₂ (Nat.castRingHom ℝ) activity =
      includedPartition m (2 * k + 1) activity := by
  have h := congrArg (fun p : ℕ[X] => p.eval₂ (Nat.castRingHom ℝ) activity)
    (conditionalPolynomials_graph m k).2
  rw [eval₂_add, conditionalPolynomials_excluded] at h
  unfold includedPartition totalPartition
  rw [ForestExpr.graph_polynomial]
  linarith

theorem conditionalPolynomials_total (m k : ℕ) :
    (conditionalPolynomials m k).1 + (conditionalPolynomials m k).2 =
      independencePolynomial (sphericalTree m (2 * k + 1)).graph Finset.univ := by
  rw [ForestExpr.graph_polynomial]
  exact (conditionalPolynomials_graph m k).2

end SphericalTreeFailures
