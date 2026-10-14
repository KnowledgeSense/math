import MainTheorems.DiagonalSchatten.CompressionRegularity
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Polynomial

variable {J : Type*} [Fintype J]

def rowMinor (B : Matrix (Fin 2) J ℝ) (j k : J) : ℝ := B 0 j * B 1 k - B 1 j * B 0 k

theorem zero_gram_minor (X : Matrix (Fin 2) J ℝ)
    (hdet : gramFirst X * gramSecond X - gramCross X ^ 2 = 0) (j k : J) :
    rowMinor X j k = 0 := by
  have hsq := areaVector_norm_sq X
  rw [hdet] at hsq
  have hn : ‖areaVector X‖ = 0 := by nlinarith [norm_nonneg (areaVector X)]
  have hz := norm_eq_zero.mp hn
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (J × J) => v (j, k)) hz
  change rowMinor X j k = 0 at hcoord
  exact hcoord

theorem nonzero_minor_gram_positive (X : Matrix (Fin 2) J ℝ) {j k : J}
    (hminor : rowMinor X j k ≠ 0) :
    0 < gramFirst X * gramSecond X - gramCross X ^ 2 := by
  have hsq := areaVector_norm_sq X
  have hdet : 0 ≤ gramFirst X * gramSecond X - gramCross X ^ 2 := by
    nlinarith [sq_nonneg ‖areaVector X‖]
  have hn : gramFirst X * gramSecond X - gramCross X ^ 2 ≠ 0 := by
    intro h
    exact hminor (zero_gram_minor X h j k)
  exact lt_of_le_of_ne hdet (Ne.symm hn)

omit [Fintype J] in
theorem realEntryRoot_minor_zero_iff {p : ℝ} (hp : 0 < p)
    (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j) (j k : J) :
    rowMinor (realEntryRoot p B) j k = 0 ↔ rowMinor B j k = 0 := by
  change B 0 j ^ (1 / p) * B 1 k ^ (1 / p) -
    B 1 j ^ (1 / p) * B 0 k ^ (1 / p) = 0 ↔ B 0 j * B 1 k - B 1 j * B 0 k = 0
  rw [sub_eq_zero, sub_eq_zero, ← Real.mul_rpow (hB 0 j).le (hB 1 k).le,
    ← Real.mul_rpow (hB 1 j).le (hB 0 k).le]
  exact Real.rpow_left_inj (mul_pos (hB 0 j) (hB 1 k)).le
    (mul_pos (hB 1 j) (hB 0 k)).le (one_div_ne_zero hp.ne')

def affineArray (B E : Matrix (Fin 2) J ℝ) (t : ℝ) : Matrix (Fin 2) J ℝ :=
  Matrix.of fun i j => B i j + t * E i j

def affineMinorPolynomial (B E : Matrix (Fin 2) J ℝ) (j k : J) : ℝ[X] :=
  (Polynomial.C (B 0 j) + Polynomial.X * Polynomial.C (E 0 j)) *
    (Polynomial.C (B 1 k) + Polynomial.X * Polynomial.C (E 1 k)) -
  (Polynomial.C (B 1 j) + Polynomial.X * Polynomial.C (E 1 j)) *
    (Polynomial.C (B 0 k) + Polynomial.X * Polynomial.C (E 0 k))

omit [Fintype J] in
theorem affineMinorPolynomial_eval (B E : Matrix (Fin 2) J ℝ) (j k : J) (t : ℝ) :
    (affineMinorPolynomial B E j k).eval t = rowMinor (affineArray B E t) j k := by
  simp [affineMinorPolynomial, affineArray, rowMinor]
  ring

omit [Fintype J] in
theorem affineMinorPolynomial_degree (B E : Matrix (Fin 2) J ℝ) (j k : J) :
    (affineMinorPolynomial B E j k).natDegree ≤ 2 := by
  unfold affineMinorPolynomial
  compute_degree

omit [Fintype J] in
theorem affineMinorPolynomial_nonzero (B E : Matrix (Fin 2) J ℝ) {j k : J}
    (hminor : rowMinor B j k ≠ 0) : affineMinorPolynomial B E j k ≠ 0 := by
  intro h
  have hv := congrArg (fun q : ℝ[X] => q.eval 0) h
  rw [affineMinorPolynomial_eval] at hv
  simp only [Polynomial.eval_zero, affineArray, rowMinor, zero_mul, add_zero, Matrix.of_apply] at hv
  exact hminor hv

theorem finite_rank_loss {p : ℝ} (hp : 0 < p) (B E : Matrix (Fin 2) J ℝ)
    {j k : J} (hminor : rowMinor B j k ≠ 0) :
    ∃ s : Finset ℝ, s.card ≤ 2 ∧ ∀ t : ℝ,
      (∀ i j, 0 < affineArray B E t i j) →
      gramFirst (realEntryRoot p (affineArray B E t)) *
          gramSecond (realEntryRoot p (affineArray B E t)) -
        gramCross (realEntryRoot p (affineArray B E t)) ^ 2 = 0 → t ∈ s := by
  classical
  let q := affineMinorPolynomial B E j k
  have hq : q ≠ 0 := affineMinorPolynomial_nonzero B E hminor
  refine ⟨q.roots.toFinset, ?_, ?_⟩
  · exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' q).trans (affineMinorPolynomial_degree B E j k))
  · intro t ht hdet
    have hx := zero_gram_minor (realEntryRoot p (affineArray B E t)) hdet j k
    have hb := (realEntryRoot_minor_zero_iff hp _ ht j k).mp hx
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hq).mpr
    change q.eval t = 0
    exact (affineMinorPolynomial_eval B E j k t).trans hb

variable [DecidableEq J]

def perturbFirstCoordinate (B : Matrix (Fin 2) J ℝ) (j : J) (e : ℝ) :
    Matrix (Fin 2) J ℝ := Matrix.of fun i k => if i = 0 ∧ k = j then B i k + e else B i k

omit [Fintype J] in
theorem perturbFirstCoordinate_minor (B : Matrix (Fin 2) J ℝ) {j k : J}
    (hjk : j ≠ k) (e : ℝ) :
    rowMinor (perturbFirstCoordinate B j e) j k = rowMinor B j k + e * B 1 k := by
  simp [rowMinor, perturbFirstCoordinate, Ne.symm hjk]
  ring

omit [Fintype J] in
theorem perturbFirstCoordinate_rank (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    {j k : J} (hjk : j ≠ k) (hminor : rowMinor B j k = 0) {e : ℝ} (he : 0 < e) :
    rowMinor (perturbFirstCoordinate B j e) j k ≠ 0 := by
  rw [perturbFirstCoordinate_minor B hjk, hminor, zero_add]
  exact (mul_pos he (hB 1 k)).ne'

omit [Fintype J] in
theorem perturbFirstCoordinate_positive (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (j : J) {e : ℝ} (he : 0 ≤ e) : ∀ i k, 0 < perturbFirstCoordinate B j e i k := by
  intro i k
  simp only [perturbFirstCoordinate, Matrix.of_apply]
  split_ifs
  · exact add_pos_of_pos_of_nonneg (hB i k) he
  · exact hB i k

omit [Fintype J] in
theorem continuous_perturbFirstCoordinate (B : Matrix (Fin 2) J ℝ) (j : J) :
    Continuous (perturbFirstCoordinate B j) := by
  change Continuous (fun e : ℝ => fun i k => if i = 0 ∧ k = j then B i k + e else B i k)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  by_cases h : i = 0 ∧ k = j
  · simp only [ite_eq_left h]
    fun_prop
  · simp only [ite_eq_right h]
    fun_prop

end

end ResearchMain.DiagonalSchatten
