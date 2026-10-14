import HardCoreActivityThreshold.ScalarFunctions
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace HardCoreActivityThreshold

set_option maxHeartbeats 2000000

noncomputable def thirdPartitionDerivative (x : ℝ) : ℝ :=
  (-6+8*scalarOccupation x)*(1-scalarOccupation x)*potential (remainingPotential x)+
    (1-scalarOccupation x)*(7-2*(scalarOccupation x)⁻¹)*potentialDerivative (remainingPotential x)+
    3*(1-scalarOccupation x)*(scalarOccupation x)⁻¹*potentialSecondDerivative (remainingPotential x)-
    6*cubicCoefficient*(scalarOccupation x)⁻¹

theorem secondPartitionDerivative_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt secondPartitionDerivative (thirdPartitionDerivative x) x := by
  have hq := occupation_hasDerivAt x
  have hy := remainingPotential_hasDerivAt x hx
  have hp := (potential_hasDerivAt (remainingPotential x)).comp x hy
  have hp1 := (potentialDerivative_hasDerivAt (remainingPotential x)).comp x hy
  have hp2 := (potentialSecondDerivative_hasDerivAt (remainingPotential x)).comp x hy
  have h1 := (hasDerivAt_const x (1 : ℝ)).sub hq
  have h2 := (hasDerivAt_const x (1 : ℝ)).sub (hq.const_mul 2)
  have hd := (((h1.const_mul 2).mul h2).mul hp).sub
    ((h1.const_mul 3).mul hp1) |>.add hp2
  convert hd using 1
  · rfl
  · simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply]
    unfold thirdPartitionDerivative
    have hqn := (occupation_pos x hx).ne'
    field_simp
    ring

noncomputable def fourthNumerator (q y : ℝ) : ℝ :=
  (q-1)*(15*cubicCoefficient*q^2*cubicCenter^2-6*cubicCoefficient*q*cubicCenter^2-
    28*cubicCoefficient*q*cubicCenter-2*cubicCoefficient*cubicCenter^2-
    4*cubicCoefficient*cubicCenter+12*cubicCoefficient+15*q^2-6*q-2)+
  2*(q-1)*(8*cubicCoefficient*q^3*cubicCenter^2-7*cubicCoefficient*q^2*cubicCenter^2-
    30*cubicCoefficient*q^2*cubicCenter+12*cubicCoefficient*q*cubicCenter+
    21*cubicCoefficient*q+4*cubicCoefficient*cubicCenter+3*cubicCoefficient+8*q^3-7*q^2)*y-
  cubicCoefficient*(q-1)*(32*q^3*cubicCenter-28*q^2*cubicCenter-45*q^2+18*q+6)*y^2+
  2*cubicCoefficient*q^2*(q-1)*(8*q-7)*y^3

noncomputable def fourthPartitionDerivative (x : ℝ) : ℝ :=
  fourthNumerator (scalarOccupation x) (remainingPotential x)/(scalarOccupation x)^2

theorem thirdPartitionDerivative_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt thirdPartitionDerivative (fourthPartitionDerivative x) x := by
  have hq := occupation_hasDerivAt x
  have hy := remainingPotential_hasDerivAt x hx
  have hp := (potential_hasDerivAt (remainingPotential x)).comp x hy
  have hp1 := (potentialDerivative_hasDerivAt (remainingPotential x)).comp x hy
  have hp2 := (potentialSecondDerivative_hasDerivAt (remainingPotential x)).comp x hy
  have hi := hq.inv (occupation_pos x hx).ne'
  have h1 := (hasDerivAt_const x (1 : ℝ)).sub hq
  have ha := (hq.const_mul 8).const_add (-6)
  have hb := (hasDerivAt_const x (7 : ℝ)).sub (hi.const_mul 2)
  have hd := (((ha.mul h1).mul hp).add ((h1.mul hb).mul hp1)).add
    (((h1.const_mul 3).mul hi).mul hp2) |>.sub (hi.const_mul (6*cubicCoefficient))
  convert hd using 1
  · rfl
  · simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply, Pi.inv_apply]
    unfold fourthPartitionDerivative fourthNumerator potential cubicPotential
      potentialDerivative potentialSecondDerivative
    have hqn := (occupation_pos x hx).ne'
    field_simp
    ring

end HardCoreActivityThreshold
