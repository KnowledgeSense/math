import MainTheorems.DiagonalSchatten.SymmetricPowerDifferential
import MainTheorems.DiagonalSchatten.CompressionGradient

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

def gramCoordinates (X : Matrix (Fin 2) J ℝ) : Fin 3 → ℝ :=
  ![gramFirst X, gramSecond X, gramCross X]

def gramVariation (X Y : Matrix (Fin 2) J ℝ) : Fin 3 → ℝ :=
  ![2 * ∑ j, X 0 j * Y 0 j, 2 * ∑ j, X 1 j * Y 1 j,
    ∑ j, (Y 0 j * X 1 j + X 0 j * Y 1 j)]

theorem gramCoordinates_hasFDerivAt (X : Matrix (Fin 2) J ℝ) :
    HasFDerivAt gramCoordinates
      (ContinuousLinearMap.pi
        ![fderiv ℝ gramFirst X, fderiv ℝ gramSecond X, fderiv ℝ gramCross X]) X := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (show DifferentiableAt ℝ gramFirst X by unfold gramFirst; fun_prop).hasFDerivAt
  · exact (show DifferentiableAt ℝ gramSecond X by unfold gramSecond; fun_prop).hasFDerivAt
  · exact (show DifferentiableAt ℝ gramCross X by unfold gramCross; fun_prop).hasFDerivAt

theorem fderiv_gramCoordinates (X Y : Matrix (Fin 2) J ℝ) :
    fderiv ℝ gramCoordinates X Y = gramVariation X Y := by
  rw [(gramCoordinates_hasFDerivAt X).fderiv]
  funext i
  fin_cases i <;> simp [gramVariation, ContinuousLinearMap.pi_apply,
    fderiv_gramFirst, fderiv_gramSecond, fderiv_gramCross]

variable [DecidableEq J] [Nonempty J]

omit [DecidableEq J] [Nonempty J] in
theorem gramCoordinates_entryRoot_curve (p : ℝ)
    (B E : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j) :
    HasDerivAt (fun t : ℝ => gramCoordinates (realEntryRoot p (rowDirection B E t)))
      (gramVariation (realEntryRoot p B) (entryRootDirection p B E)) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun t => gramFirst (realEntryRoot p (rowDirection B E t)))
      (2 * ∑ j, realEntryRoot p B 0 j * entryRootDirection p B E 0 j) 0
    have h := (show DifferentiableAt ℝ gramFirst (realEntryRoot p B) by
      unfold gramFirst; fun_prop).hasFDerivAt.comp_hasDerivAt_of_eq 0
        (realEntryRoot_direction_deriv p B E hB) (by rw [rowDirection_zero])
    convert! h using 1
    exact (fderiv_gramFirst _ _).symm
  · change HasDerivAt (fun t => gramSecond (realEntryRoot p (rowDirection B E t)))
      (2 * ∑ j, realEntryRoot p B 1 j * entryRootDirection p B E 1 j) 0
    have h := (show DifferentiableAt ℝ gramSecond (realEntryRoot p B) by
      unfold gramSecond; fun_prop).hasFDerivAt.comp_hasDerivAt_of_eq 0
        (realEntryRoot_direction_deriv p B E hB) (by rw [rowDirection_zero])
    convert! h using 1
    exact (fderiv_gramSecond _ _).symm
  · change HasDerivAt (fun t => gramCross (realEntryRoot p (rowDirection B E t)))
      (∑ j, (entryRootDirection p B E 0 j * realEntryRoot p B 1 j +
        realEntryRoot p B 0 j * entryRootDirection p B E 1 j)) 0
    have h := (show DifferentiableAt ℝ gramCross (realEntryRoot p B) by
      unfold gramCross; fun_prop).hasFDerivAt.comp_hasDerivAt_of_eq 0
        (realEntryRoot_direction_deriv p B E hB) (by rw [rowDirection_zero])
    convert! h using 1
    exact (fderiv_gramCross _ _).symm

omit [DecidableEq J] in
theorem realGramPowerCoefficient_entryRoot_curve (p r : ℝ)
    (B E : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) :
    HasDerivAt (fun t : ℝ => realGramPowerCoefficient r (realEntryRoot p (rowDirection B E t)))
      (symmetricPowerVariation r (gramCoordinates (realEntryRoot p B))
        (gramVariation (realEntryRoot p B) (entryRootDirection p B E))) 0 := by
  let X := realEntryRoot p B
  let m := gramCoordinates X
  have hX : ∀ i j, 0 < X i j := fun i j => Real.rpow_pos_of_pos (hB i j) _
  have hc : gramCross X ≠ 0 :=
    (Finset.sum_pos (fun j _ => mul_pos (hX 0 j) (hX 1 j)) Finset.univ_nonempty).ne'
  have hmp : symmetricPlus m ≠ 0 := by
    change realGramPlus X ≠ 0
    exact (realGram_eigenvalues_positive X hdet).1.ne'
  have hmm : symmetricMinus m ≠ 0 := by
    change realGramMinus X ≠ 0
    exact (realGram_eigenvalues_positive X hdet).2.ne'
  have hmc : m 2 ≠ 0 := hc
  have hD := (contDiffAt_symmetricPower (n := 1) r m hmc hmp hmm).differentiableAt (by norm_num)
  have hcurve := hD.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (gramCoordinates_entryRoot_curve p B E hB) (by rw [rowDirection_zero])
  rw [fderiv_symmetricPower r m _ hmc hmp hmm] at hcurve
  convert! hcurve using 1

end

end ResearchMain.DiagonalSchatten
