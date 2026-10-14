import HardCoreActivityThreshold.FourthDerivativeBounds
import HardCoreActivityThreshold.StationaryPoint
import HardCoreActivityThreshold.ScalarCoordinates

namespace HardCoreActivityThreshold
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

noncomputable def expandedFourth (q y z : ℝ) : ℝ :=
  ((0.256)*q*q*q*q*y*y*y)+
    ((-0.512)*q*q*q*q*y*y*z)+
    ((0.256)*q*q*q*q*y*z*z)+
    ((16)*q*q*q*q*y)+
    ((-0.48)*q*q*q*y*y*y)+
    ((0.96)*q*q*q*y*y*z)+
    ((0.72)*q*q*q*y*y)+
    ((-0.48)*q*q*q*y*z*z)+
    ((-0.96)*q*q*q*y*z)+
    ((-30)*q*q*q*y)+
    ((0.24)*q*q*q*z*z)+
    ((15)*q*q*q)+
    ((0.224)*q*q*y*y*y)+
    ((-0.448)*q*q*y*y*z)+
    ((-1.008)*q*q*y*y)+
    ((0.224)*q*q*y*z*z)+
    ((1.344)*q*q*y*z)+
    ((14.672)*q*q*y)+
    ((-0.336)*q*q*z*z)+
    ((-0.448)*q*q*z)+
    ((-21)*q*q)+
    ((0.192)*q*y*y)+
    ((-0.256)*q*y*z)+
    ((-0.576)*q*y)+
    ((0.064)*q*z*z)+
    ((0.384)*q*z)+
    ((4.192)*q)+
    ((0.096)*y*y)+
    ((-0.128)*y*z)+
    ((-0.096)*y)+
    ((0.032)*z*z)+
    ((0.064)*z)+
    ((1.808))
noncomputable def expandedSecond (q y z : ℝ) : ℝ :=
  ((0.064)*q*q*y*y*y)+
    ((-0.128)*q*q*y*y*z)+
    ((0.064)*q*q*y*z*z)+
    ((4)*q*q*y)+
    ((-0.096)*q*y*y*y)+
    ((0.192)*q*y*y*z)+
    ((0.144)*q*y*y)+
    ((-0.096)*q*y*z*z)+
    ((-0.192)*q*y*z)+
    ((-6)*q*y)+
    ((0.048)*q*z*z)+
    ((3)*q)+
    ((0.032)*y*y*y)+
    ((-0.064)*y*y*z)+
    ((-0.144)*y*y)+
    ((0.032)*y*z*z)+
    ((0.192)*y*z)+
    ((2.096)*y)+
    ((-0.048)*z*z)+
    ((-0.064)*z)+
    ((-3))

theorem fourthNumerator_expanded (q y : ℝ) :
    fourthNumerator q y=expandedFourth q y cubicCenter := by
  unfold fourthNumerator expandedFourth cubicCoefficient
  ring

theorem secondPartitionDerivative_expanded (x : ℝ) :
    secondPartitionDerivative x=expandedSecond (scalarOccupation x) (remainingPotential x) cubicCenter := by
  unfold secondPartitionDerivative expandedSecond potential cubicPotential potentialDerivative
    potentialSecondDerivative cubicCoefficient
  ring

end HardCoreActivityThreshold
