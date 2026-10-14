import MainTheorems.DiagonalSchatten.Basic

namespace ResearchMain.DiagonalSchatten

open scoped BigOperators Polynomial

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def rootPowerSum (p : ℝ) (A : Matrix I I ℂ) : ℝ :=
  (A.charpoly.roots.map fun z => (Real.sqrt z.re) ^ p).sum

theorem schattenPower_eq_gram_roots (p : ℝ) (A : Matrix I J ℂ) :
    schattenPower p A = rootPowerSum p (A.conjTranspose * A) := by
  rw [rootPowerSum,
    (Matrix.isHermitian_conjTranspose_mul_self A).roots_charpoly_eq_eigenvalues₀]
  simp only [Multiset.map_map, Function.comp_def]
  change (∑ i : Fin (Fintype.card J), (A.toEuclideanLin.singularValues i) ^ p) =
    ∑ i : Fin (Fintype.card J),
      (Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ i)) ^ p
  apply Finset.sum_congr rfl
  intro i _
  rw [A.toEuclideanLin.singularValues_fin finrank_euclideanSpace]
  unfold Matrix.IsHermitian.eigenvalues₀
  simp only [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

theorem rootPowerSum_gram_comm {p : ℝ} (hp : 0 < p) (A : Matrix I J ℂ) :
    rootPowerSum p (A * A.conjTranspose) = rootPowerSum p (A.conjTranspose * A) := by
  have h := congrArg Polynomial.roots (Matrix.charpoly_mul_comm' A A.conjTranspose)
  have hleft : (Polynomial.X : ℂ[X]) ^ Fintype.card J *
      (A * A.conjTranspose).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero
  have hright : (Polynomial.X : ℂ[X]) ^ Fintype.card I *
      (A.conjTranspose * A).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero
  rw [Polynomial.roots_mul hleft, Polynomial.roots_mul hright] at h
  have hs := congrArg (fun s : Multiset ℂ =>
    (s.map fun z => (Real.sqrt z.re) ^ p).sum) h
  simpa [rootPowerSum, Polynomial.roots_X_pow, Multiset.nsmul_singleton,
    Real.zero_rpow hp.ne'] using hs

theorem schattenPower_eq_row_gram_roots {p : ℝ} (hp : 0 < p) (A : Matrix I J ℂ) :
    schattenPower p A = rootPowerSum p (A * A.conjTranspose) := by
  rw [schattenPower_eq_gram_roots, rootPowerSum_gram_comm hp]

theorem schattenPower_conjTranspose {p : ℝ} (hp : 0 < p) (A : Matrix I J ℂ) :
    schattenPower p A.conjTranspose = schattenPower p A := by
  rw [schattenPower_eq_gram_roots, Matrix.conjTranspose_conjTranspose,
    rootPowerSum_gram_comm hp, schattenPower_eq_gram_roots]

theorem schattenNorm_conjTranspose {p : ℝ} (hp : 0 < p) (A : Matrix I J ℂ) :
    schattenNorm p A.conjTranspose = schattenNorm p A := by
  unfold schattenNorm
  rw [schattenPower_conjTranspose hp]

end ResearchMain.DiagonalSchatten
