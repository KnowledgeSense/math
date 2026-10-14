import MainTheorems.DiagonalSchatten.TwoColumnRayBound
import MainTheorems.DiagonalSchatten.PowerVariationContinuity

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

variable {J : Type*} [Fintype J]

theorem continuous_gramCoordinates : Continuous (gramCoordinates (J := J)) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [gramCoordinates] <;>
    simp only [gramFirst, gramSecond, gramCross] <;> fun_prop

theorem gramFirst_positive_of_determinant (X : Matrix (Fin 2) J ℝ)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) : 0 < gramFirst X := by
  have hA : 0 ≤ gramFirst X := Finset.sum_nonneg fun j _ => sq_nonneg _
  by_contra hn
  have hz : gramFirst X = 0 := le_antisymm (le_of_not_gt hn) hA
  rw [hz] at hdet
  nlinarith [sq_nonneg (gramCross X)]

theorem continuousAt_realGramPowerCoefficient (r : ℝ) (X : Matrix (Fin 2) J ℝ)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) (hc : gramCross X ≠ 0) :
    ContinuousAt (realGramPowerCoefficient r) X := by
  have hM : 0 < gramCoordinates X 0 := gramFirst_positive_of_determinant X hdet
  obtain ⟨hm, hp⟩ := symmetricEigenvalues_positive hM hdet
  have hpower := (contDiffAt_symmetricPower (n := 0) r (gramCoordinates X) hc hp.ne' hm.ne').continuousAt
  have h := hpower.comp continuous_gramCoordinates.continuousAt
  simpa only [Function.comp_def, gramCoordinates, symmetricPower_gram] using h

theorem continuousAt_compressionRay_functional (p : ℝ) (X : Matrix (Fin 2) J ℝ)
    (Z : Fin 3 → ℝ) (j : J) (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2)
    (hc : gramCross X ≠ 0)
    (hD : (compressionRay p X Z).denominator (fun i => X i j) ≠ 0) :
    ContinuousAt (fun Y => (compressionRay p Y Z).functional (fun i => Y i j)) X := by
  have hH := continuousAt_realGramPowerCoefficient ((p - 2) / 2) X hdet hc
  have h0 : ContinuousAt (fun Y : Matrix (Fin 2) J ℝ =>
      realGramPowerCoefficient ((p - 2) / 2) Y 0) X :=
    (continuous_apply 0).continuousAt.comp hH
  have h1 : ContinuousAt (fun Y : Matrix (Fin 2) J ℝ =>
      realGramPowerCoefficient ((p - 2) / 2) Y 1) X :=
    (continuous_apply 1).continuousAt.comp hH
  have h2 : ContinuousAt (fun Y : Matrix (Fin 2) J ℝ =>
      realGramPowerCoefficient ((p - 2) / 2) Y 2) X :=
    (continuous_apply 2).continuousAt.comp hH
  have hu : ContinuousAt (fun Y : Matrix (Fin 2) J ℝ => Y 0 j) X :=
    (continuous_apply j).continuousAt.comp (continuous_apply 0).continuousAt
  have hv : ContinuousAt (fun Y : Matrix (Fin 2) J ℝ => Y 1 j) X :=
    (continuous_apply j).continuousAt.comp (continuous_apply 1).continuousAt
  have hi0 : ContinuousAt (fun Y : Matrix (Fin 2) J ℝ => Z 0 * Y 0 j + Z 2 * Y 1 j) X :=
    (continuousAt_const.mul hu).add (continuousAt_const.mul hv)
  have hi1 : ContinuousAt (fun Y : Matrix (Fin 2) J ℝ => Z 2 * Y 0 j + Z 1 * Y 1 j) X :=
    (continuousAt_const.mul hu).add (continuousAt_const.mul hv)
  have hnum : ContinuousAt (fun Y => (compressionRay p Y Z).numerator (fun i => Y i j)) X := by
    dsimp [RayParameters.numerator, RayParameters.image, compressionRay]
    exact ((((continuousAt_const.mul h1).mul hu).mul hv).add
        ((continuousAt_const.mul h2).mul (hu.pow 2))).mul (hi0.pow 2) |>.add
      (((((continuousAt_const.mul h2).mul hu).mul hv).mul hi0).mul hi1) |>.add
      (((((continuousAt_const.mul h0).mul hu).mul hv).add
        ((continuousAt_const.mul h2).mul (hv.pow 2))).mul (hi1.pow 2))
  have hden : ContinuousAt (fun Y => (compressionRay p Y Z).denominator (fun i => Y i j)) X := by
    dsimp [RayParameters.denominator, compressionRay]
    exact continuousAt_const.mul
      (((((continuousAt_const.mul h0).mul h2).mul (hu.pow 2)).add
        ((((continuousAt_const.mul h0).mul h1).add
          (continuousAt_const.mul (h2.pow 2))).mul hu |>.mul hv)).add
        (((continuousAt_const.mul h1).mul h2).mul (hv.pow 2)))
  exact hnum.div hden hD

theorem continuousAt_inverseGramQuadratic {p : ℝ} (hp2 : p ≠ 2)
    (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) (hc : 0 < gramCross X) :
    ContinuousAt (fun Y => inverseGramQuadratic p Y Z) X := by
  have hg : (p - 2) / 2 ≠ 0 := by exact div_ne_zero (sub_ne_zero.mpr hp2) (by norm_num)
  have h := (continuousAt_inversePowerQuadratic hg (gramCoordinates X) Z
    (gramFirst_positive_of_determinant X hdet) hdet hc).comp
    continuous_gramCoordinates.continuousAt
  exact h

theorem compressionRay_denominator_nonnegative {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2)
    (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ) (x : Fin 2 → ℝ)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) (hc : 0 < gramCross X)
    (hx : ∀ i, 0 ≤ x i) (hn : 0 < x 0 ∨ 0 < x 1) :
    0 < (compressionRay p X Z).denominator x := by
  let g := compressionRay p X Z
  have hM := gramFirst_positive_of_determinant X hdet
  obtain ⟨ha, hb, hd⟩ := symmetricPower_positive_definite ((p - 2) / 2)
    (gramCoordinates X) hM hdet hc.ne'
  simp only [gramCoordinates, symmetricPower_gram] at ha hb hd
  rcases lt_or_gt_of_ne hp2 with hp2 | hp2
  · have hcross := symmetricPower_cross_negative (by linarith : (p - 2) / 2 < 0)
      (gramCoordinates X) hM hdet hc
    simp only [gramCoordinates, symmetricPower_gram] at hcross
    exact g.denominator_lower x (by change -1 < p - 2; linarith)
      (by change p - 2 < 0; linarith) ha hb hcross (sub_pos.mp hd) (hx 0) (hx 1) hn
  · have hcross := symmetricPower_cross_positive (by linarith : 0 < (p - 2) / 2)
      (gramCoordinates X) hM hdet hc
    simp only [gramCoordinates, symmetricPower_gram] at hcross
    exact g.denominator_upper x (by change 0 < p - 2; linarith)
      ha hb hcross (hx 0) (hx 1) hn

end

end ResearchMain.DiagonalSchatten
