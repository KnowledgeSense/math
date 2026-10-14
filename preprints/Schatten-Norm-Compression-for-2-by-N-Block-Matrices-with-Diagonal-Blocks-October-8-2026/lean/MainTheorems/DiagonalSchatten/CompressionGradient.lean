import MainTheorems.DiagonalSchatten.TwoRowPowerConnection
import MainTheorems.DiagonalSchatten.CompressionHomogeneity
import MainTheorems.DiagonalSchatten.RankLoss
import Mathlib.Analysis.Calculus.Deriv.Pi

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J] [DecidableEq J]

def entryRootDirection (p : ℝ) (B E : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) J ℝ :=
  Matrix.of fun i j => (1 / p) * B i j ^ (1 / p - 1) * E i j

omit [DecidableEq J] in
theorem realEntryRoot_direction_deriv (p : ℝ) (B E : Matrix (Fin 2) J ℝ)
    (hB : ∀ i j, 0 < B i j) :
    HasDerivAt (fun t : ℝ => realEntryRoot p (rowDirection B E t))
      (entryRootDirection p B E) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have he := ((hasDerivAt_const (0 : ℝ) (B i j)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (E i j))).rpow_const (p := 1 / p)
      (Or.inl (by simpa using (hB i j).ne'))
  convert! he using 1
  simp [entryRootDirection]
  ring

omit [DecidableEq J] in
theorem fderiv_realEntryRoot (p : ℝ) (B E : Matrix (Fin 2) J ℝ)
    (hB : ∀ i j, 0 < B i j) :
    fderiv ℝ (realEntryRoot p) B E = entryRootDirection p B E := by
  have hd := (contDiffAt_realEntryRoot (n := 1) p B hB).differentiableAt (by norm_num)
  have he := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (rowDirection_hasDerivAt B E)
    (rowDirection_zero B E).symm
  exact he.unique (realEntryRoot_direction_deriv p B E hB)

def compressionGradient (p : ℝ) (B : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) J ℝ :=
  let X := realEntryRoot p B
  let Z := realGramPowerCoefficient ((p - 2) / 2) X
  Matrix.of fun i j =>
    (if i = 0 then Z 0 * X 0 j + Z 2 * X 1 j else Z 2 * X 0 j + Z 1 * X 1 j) *
      B i j ^ (1 / p - 1)

theorem fderiv_compressionFunctional [Nonempty J] {p : ℝ} (hp : 0 < p)
    (B E : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) :
    fderiv ℝ (compressionFunctional p) B E =
      ∑ j, (compressionGradient p B 0 j * E 0 j + compressionGradient p B 1 j * E 1 j) := by
  let X := realEntryRoot p B
  let U := entryRootDirection p B E
  let Z := realGramPowerCoefficient ((p - 2) / 2) X
  have hX : ∀ i j, 0 < X i j := fun i j => Real.rpow_pos_of_pos (hB i j) _
  have hc : gramCross X ≠ 0 :=
    (Finset.sum_pos (fun j _ => mul_pos (hX 0 j) (hX 1 j)) Finset.univ_nonempty).ne'
  have hdS := (contDiffAt_schattenPower_complexify_fullRank (n := 1) hp X hc hdet).differentiableAt
    (by norm_num)
  have hdR := (contDiffAt_realEntryRoot (n := 1) p B hB).differentiableAt (by norm_num)
  have hchain := congrArg (fun L : Matrix (Fin 2) J ℝ →L[ℝ] ℝ => L E)
    (fderiv_comp B hdS hdR)
  change fderiv ℝ (compressionFunctional p) B E = _ at hchain
  rw [hchain]
  change fderiv ℝ (fun A : Matrix (Fin 2) J ℝ => schattenPower p (complexifyRows A))
    (realEntryRoot p B) (fderiv ℝ (realEntryRoot p) B E) = _
  rw [fderiv_realEntryRoot p B E hB]
  change fderiv ℝ (fun A : Matrix (Fin 2) J ℝ => schattenPower p (complexifyRows A)) X U = _
  rw [fderiv_schattenPower_complexify hp X U hc hdet,
    fderiv_gramFirst, fderiv_gramSecond, fderiv_gramCross]
  change (p / 2) * (Z 0 * (2 * ∑ j, X 0 j * U 0 j) +
    Z 1 * (2 * ∑ j, X 1 j * U 1 j) +
    2 * Z 2 * (∑ j, (U 0 j * X 1 j + X 0 j * U 1 j))) = _
  have he : (p / 2) * (Z 0 * (2 * ∑ j, X 0 j * U 0 j) +
      Z 1 * (2 * ∑ j, X 1 j * U 1 j) +
      2 * Z 2 * (∑ j, (U 0 j * X 1 j + X 0 j * U 1 j))) =
      ∑ j, ((p / 2) * (Z 0 * (2 * X 0 j * U 0 j) +
        Z 1 * (2 * X 1 j * U 1 j) + 2 * Z 2 * (U 0 j * X 1 j + X 0 j * U 1 j))) := by
    simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  simp only [U, entryRootDirection, compressionGradient, Matrix.of_apply, Z, X,
    ite_true, Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  field_simp [hp.ne']
  ring

end

end ResearchMain.DiagonalSchatten
