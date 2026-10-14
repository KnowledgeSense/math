import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace HardCoreActivityThreshold

noncomputable def criticalOccupation : ℝ := 1/Real.sqrt 5
noncomputable def criticalActivity : ℝ := criticalOccupation/(1-criticalOccupation)^6
noncomputable def criticalLog : ℝ := -Real.log (1-criticalOccupation)
noncomputable def criticalPotential : ℝ := 5*criticalLog
noncomputable def criticalSlope : ℝ := 2*criticalOccupation*(1-criticalOccupation)/(1+criticalOccupation)
noncomputable def cubicCoefficient : ℝ := 2/125
noncomputable def slopeDefect : ℝ := criticalSlope-1/criticalPotential
noncomputable def cubicDisplacement : ℝ :=
  slopeDefect/(cubicCoefficient*(1+Real.sqrt (1-slopeDefect^2/cubicCoefficient)))
noncomputable def cubicCenter : ℝ := criticalPotential-cubicDisplacement
noncomputable def cubicPotential (z y : ℝ) : ℝ := y*(1+cubicCoefficient*(y-z)^2)
noncomputable def potential : ℝ → ℝ := cubicPotential cubicCenter

@[simp] theorem cubicPotential_zero (z : ℝ) : cubicPotential z 0=0 := by simp [cubicPotential]
theorem cubicCoefficient_pos : 0<cubicCoefficient := by norm_num [cubicCoefficient]
theorem cubicPotential_ge (z y : ℝ) (hy : 0≤y) : y≤cubicPotential z y := by
  unfold cubicPotential
  nlinarith [sq_nonneg (y-z),mul_nonneg hy (mul_nonneg cubicCoefficient_pos.le (sq_nonneg (y-z)))]
theorem cubicPotential_nonneg (z y : ℝ) (hy : 0≤y) : 0≤cubicPotential z y :=
  hy.trans (cubicPotential_ge z y hy)

theorem cubicPotential_hasDerivAt (z y : ℝ) :
    HasDerivAt (cubicPotential z) (1+cubicCoefficient*(3*y^2-4*z*y+z^2)) y := by
  convert (hasDerivAt_id y).mul ((hasDerivAt_const y (1 : ℝ)).add
    (((hasDerivAt_id y).sub_const z).pow 2 |>.const_mul cubicCoefficient)) using 1
  · funext x
    simp [cubicPotential]
  · dsimp
    ring

theorem cubicPotential_deriv_lower (z y : ℝ) :
    1-cubicCoefficient*z^2/3≤1+cubicCoefficient*(3*y^2-4*z*y+z^2) := by
  have hs := sq_nonneg (3*y-2*z)
  norm_num [cubicCoefficient] at *
  nlinarith

theorem cubicPotential_strictMono (z : ℝ) (hz : z∈Set.Icc (28310/10000) (28311/10000)) :
    StrictMono (cubicPotential z) := by
  apply strictMono_of_deriv_pos
  intro y
  rw [(cubicPotential_hasDerivAt z y).deriv]
  have hl := cubicPotential_deriv_lower z y
  norm_num [cubicCoefficient] at hl ⊢
  have hz0 := hz.1
  have hz1 := hz.2
  nlinarith [sq_nonneg (z-28310/10000)]

theorem cubicPotential_outside (z Y : ℝ) (hz : z∈Set.Icc (28310/10000) (28311/10000))
    (hY : 0≤Y) (hout : Y≤5/2 ∨ 31/10≤Y) :
    (1001/1000)*Y≤cubicPotential z Y := by
  have hd : (1/4 : ℝ)^2≤(Y-z)^2 := by
    rcases hout with h | h
    · have hz0 := hz.1
      nlinarith [sq_nonneg (Y-z+1/4)]
    · have hz1 := hz.2
      nlinarith [sq_nonneg (Y-z-1/4)]
  unfold cubicPotential
  norm_num [cubicCoefficient] at *
  have hm := mul_le_mul_of_nonneg_left hd hY
  nlinarith

end HardCoreActivityThreshold
