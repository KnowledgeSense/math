import MainTheorems.DiagonalSchatten.GramPowerDerivative
import MainTheorems.DiagonalSchatten.CompressionHessian

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

variable {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]

def compressionGradientVariation (p : ℝ) (B E : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) J ℝ :=
  let X := realEntryRoot p B
  let Y := entryRootDirection p B E
  let H := realGramPowerCoefficient ((p - 2) / 2) X
  let D := symmetricPowerVariation ((p - 2) / 2) (gramCoordinates X) (gramVariation X Y)
  Matrix.of fun i j =>
    (if i = 0 then D 0 * X 0 j + D 2 * X 1 j + H 0 * Y 0 j + H 2 * Y 1 j
      else D 2 * X 0 j + D 1 * X 1 j + H 2 * Y 0 j + H 1 * Y 1 j) *
      B i j ^ (1 / p - 1) +
    (if i = 0 then H 0 * X 0 j + H 2 * X 1 j else H 2 * X 0 j + H 1 * X 1 j) *
      ((1 / p - 1) * B i j ^ (1 / p - 2) * E i j)

omit [DecidableEq J] in
theorem compressionGradient_curve_deriv [DecidableEq J] (p : ℝ)
    (B E : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) (i : Fin 2) (j : J) :
    HasDerivAt (fun t : ℝ => compressionGradient p (rowDirection B E t) i j)
      (compressionGradientVariation p B E i j) 0 := by
  have hX := realEntryRoot_direction_deriv p B E hB
  have hH := realGramPowerCoefficient_entryRoot_curve p ((p - 2) / 2) B E hB hdet
  have hcoord (i : Fin 2) : HasDerivAt (fun t : ℝ => rowDirection B E t i j) (E i j) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (B i j)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (E i j)) using 1
    simp
  have hpow (i : Fin 2) := (hcoord i).rpow_const (p := 1 / p - 1)
    (Or.inl (by rw [rowDirection_zero]; exact (hB i j).ne'))
  have hx (i : Fin 2) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hX i) j
  have hh (i : Fin 3) := hasDerivAt_pi.mp hH i
  fin_cases i
  · have hd := (((hh 0).mul (hx 0)).add ((hh 2).mul (hx 1))).mul (hpow 0)
    convert! hd using 1
    simp [compressionGradientVariation, rowDirection_zero]
    ring_nf
  · have hd := (((hh 2).mul (hx 0)).add ((hh 1).mul (hx 1))).mul (hpow 1)
    convert! hd using 1
    simp [compressionGradientVariation, rowDirection_zero]
    ring_nf

theorem compressionHessian_gradientVariation {p : ℝ} (hp : 1 < p)
    (B E : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) :
    compressionHessian p B E E =
      ∑ j, (compressionGradientVariation p B E 0 j * E 0 j +
        compressionGradientVariation p B E 1 j * E 1 j) := by
  have hp0 : 0 < p := by linarith
  have h2 := contDiffAt_compressionFunctional_fullRank (n := 2) hp0 B hB hdet
  have hD := (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hscalar := hD.hasFDerivAt.clm_apply (hasFDerivAt_const E B)
  have hcurve : HasDerivAt (fun t : ℝ => fderiv ℝ (compressionFunctional p) (rowDirection B E t) E)
      (compressionHessian p B E E) 0 := by
    have h := hscalar.comp_hasDerivAt_of_eq 0 (rowDirection_hasDerivAt B E)
      (rowDirection_zero B E).symm
    change HasDerivAt (fun t : ℝ => fderiv ℝ (compressionFunctional p) (rowDirection B E t) E)
      (fderiv ℝ (compressionFunctional p) B 0 + compressionHessian p B E E) 0 at h
    simpa only [ContinuousLinearMap.map_zero, zero_add] using h
  have hR := continuous_realEntryRoot hp0 (J := J)
  have hdetC : Continuous (fun Y : Matrix (Fin 2) J ℝ =>
      gramFirst (realEntryRoot p Y) * gramSecond (realEntryRoot p Y) -
        gramCross (realEntryRoot p Y) ^ 2) := by
    unfold gramFirst gramSecond gramCross
    fun_prop
  have hline : Filter.Tendsto (rowDirection B E) (𝓝 (0 : ℝ)) (𝓝 B) := by
    have h := (rowDirection_hasDerivAt B E).continuousAt.tendsto
    rw [rowDirection_zero] at h
    exact h
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i j, 0 < rowDirection B E t i j :=
    hline.eventually (positive_arrays_open.mem_nhds hB)
  have hpd : ∀ᶠ t in 𝓝 (0 : ℝ),
      0 < gramFirst (realEntryRoot p (rowDirection B E t)) *
        gramSecond (realEntryRoot p (rowDirection B E t)) -
        gramCross (realEntryRoot p (rowDirection B E t)) ^ 2 :=
    (hdetC.continuousAt.tendsto.comp hline).eventually (eventually_gt_nhds hdet)
  have heq : (fun t : ℝ => fderiv ℝ (compressionFunctional p) (rowDirection B E t) E) =ᶠ[𝓝 0]
      (fun t => ∑ j, (compressionGradient p (rowDirection B E t) 0 j * E 0 j +
        compressionGradient p (rowDirection B E t) 1 j * E 1 j)) := by
    filter_upwards [hpos, hpd] with t ht hdt
    exact fderiv_compressionFunctional hp0 _ E ht hdt
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ j, (compressionGradient p (rowDirection B E t) 0 j * E 0 j +
        compressionGradient p (rowDirection B E t) 1 j * E 1 j))
      (∑ j, (compressionGradientVariation p B E 0 j * E 0 j +
        compressionGradientVariation p B E 1 j * E 1 j)) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    exact ((compressionGradient_curve_deriv p B E hB hdet 0 j).mul_const (E 0 j)).add
      ((compressionGradient_curve_deriv p B E hB hdet 1 j).mul_const (E 1 j))
  exact hcurve.unique (hsum.congr_of_eventuallyEq heq)

end

end ResearchMain.DiagonalSchatten
