import AperyMoments.LowerEllipticRight
import AperyMoments.LowerEllipticContinuity
import AperyMoments.CandidateDensity

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

/-- The actual lower-half-plane continuation of the square-lattice elliptic expression.
The product-of-principal-powers integral fixes its branch unambiguously. -/
def continuedLattice (z : ℂ) : ℂ :=
  lowerEllipticIntegral (z / 4) / ((2 * Real.pi ^ 2 : ℝ) : ℂ)

theorem continuedLattice_analyticOnNhd :
    AnalyticOnNhd ℂ continuedLattice {z : ℂ | z.im < 0} := by
  intro z hz
  have hd : (z / 4).im < 0 := by simpa using div_neg_of_neg_of_pos hz (by norm_num : (0 : ℝ) < 4)
  exact ((lowerEllipticIntegral_analyticOnNhd (z / 4) hd).comp
    (f := fun z : ℂ => z / 4) (show AnalyticAt ℂ (fun z : ℂ => z / 4) z by fun_prop)).div_const

theorem continuedLattice_right_identity {z : ℂ} (hz : 0 < z.re) :
    continuedLattice z = complexEllipticK (1 - z ^ 2 / 16) / ((2 * Real.pi ^ 2 : ℝ) : ℂ) := by
  unfold continuedLattice
  rw [lowerEllipticIntegral_right_identity (by simpa using div_pos hz (by norm_num : (0 : ℝ) < 4))]
  congr 2
  ring_nf

theorem continuedLattice_ofReal {x : ℝ} (hx : 0 < x) :
    continuedLattice (x : ℂ) = (latticeExpression x : ℂ) := by
  unfold continuedLattice latticeExpression
  rw [show (x : ℂ) / 4 = ((x / 4 : ℝ) : ℂ) by push_cast; rfl,
    lowerEllipticIntegral_ofReal (by positivity)]
  push_cast
  congr 2
  ring_nf


theorem continuedLattice_continuousAt_right {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt continuedLattice z := by
  have hd : 0 < (z / 4).re := by simpa using div_pos hz (by norm_num : (0 : ℝ) < 4)
  exact ((lowerEllipticIntegral_differentiableAt_right hd).continuousAt.comp (f := fun z : ℂ => z / 4)
    (show ContinuousAt (fun z : ℂ => z / 4) z by fun_prop)).div_const _

theorem continuedLattice_positive_boundary {x : ℝ} (hx : 0 < x) :
    Tendsto continuedLattice (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝 (latticeExpression x : ℂ)) := by
  rw [← continuedLattice_ofReal hx]
  exact (continuedLattice_continuousAt_right hx).tendsto.mono_left nhdsWithin_le_nhds

/-- The full lower boundary connection formula on the spectral band. -/
theorem continuedLattice_negative_boundary {x : ℝ} (hx : 0 < x) (hx4 : x < 4) :
    Tendsto continuedLattice (𝓝[{z : ℂ | z.im < 0}] (-(x : ℂ)))
      (𝓝 ((latticeExpression x : ℂ) + Complex.I * (ellipticK (x ^ 2 / 16) : ℂ) /
        ((Real.pi ^ 2 : ℝ) : ℂ))) := by
  have hmap : Tendsto (fun z : ℂ => z / 4)
      (𝓝[{z : ℂ | z.im < 0}] (-(x : ℂ)))
      (𝓝[{z : ℂ | z.im < 0}] (-((x / 4 : ℝ) : ℂ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert (show Continuous (fun z : ℂ => z / 4) by fun_prop).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds using 1
      push_cast
      ring_nf
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using div_neg_of_neg_of_pos hz (by norm_num : (0 : ℝ) < 4)
  have h := ((lowerEllipticIntegral_negative_boundary
    (by positivity : 0 < x / 4) (by linarith : x / 4 < 1)).comp hmap).div_const
      (((2 * Real.pi ^ 2 : ℝ) : ℂ))
  convert h using 1
  · rfl
  · unfold latticeExpression
    rw [show (x / 4) ^ 2 = x ^ 2 / 16 by ring]
    push_cast
    ring_nf

end AperyMoments
