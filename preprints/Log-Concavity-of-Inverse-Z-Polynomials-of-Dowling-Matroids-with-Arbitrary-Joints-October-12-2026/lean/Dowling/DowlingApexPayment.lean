import Dowling.DowlingJointlessTilt

noncomputable section
namespace Dowling

/-- The exact one-apex normalized rational factor. -/
def apexClosedRatio (μ r : ℝ) : ℝ :=
  2-(r+1/2)/μ+3/(8*μ)*(1/r+1/(r+1))+1/(4*r^2*(r+1))

/-- Positive shifted numerator of the exact discrete-curvature reserve. -/
def apexPaymentReserve (x y : ℝ) : ℝ :=
    64*x^4*y^7 +
    800*x^4*y^6 +
    4048*x^4*y^5 +
    10576*x^4*y^4 +
    15076*x^4*y^3 +
    11278*x^4*y^2 +
    3721*x^4*y +
    283*x^4 +
    64*x^3*y^9 +
    1152*x^3*y^8 +
    9072*x^3*y^7 +
    40712*x^3*y^6 +
    113384*x^3*y^5 +
    199860*x^3*y^4 +
    217739*x^3*y^3 +
    (272097/2)*x^3*y^2 +
    (163267/4)*x^3*y +
    3472*x^3 +
    160*x^2*y^10 +
    2976*x^2*y^9 +
    24688*x^2*y^8 +
    120156*x^2*y^7 +
    378320*x^2*y^6 +
    798459*x^2*y^5 +
    1128607*x^2*y^4 +
    (4132645/4)*x^2*y^3 +
    (4530499/8)*x^2*y^2 +
    (2507983/16)*x^2*y +
    (110241/8)*x^2 +
    128*x*y^11 +
    2600*x*y^10 +
    23844*x*y^9 +
    130322*x*y^8 +
    470793*x*y^7 +
    (2350323/2)*x*y^6 +
    (8210467/4)*x*y^5 +
    (19835307/8)*x*y^4 +
    (31891059/16)*x*y^3 +
    (7883325/8)*x*y^2 +
    (1017633/4)*x*y +
    (89645/4)*x +
    32*y^12 +
    704*y^11 +
    7104*y^10 +
    43504*y^9 +
    179796*y^8 +
    526284*y^7 +
    1111808*y^6 +
    1693057*y^5 +
    (14579421/8)*y^4 +
    (2658625/2)*y^3 +
    606972*y^2 +
    148110*y +
    12950

theorem apexPaymentReserve_pos {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    0<apexPaymentReserve x y := by
  unfold apexPaymentReserve
  positivity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
 theorem apexPaymentReserve_identity (j r : ℝ) (hj : 1≤j) (hr : 3/2≤r) :
    (8*r^4*(j+1)*(j+r)*(r-1)^2*(r+1)^2*(r+2)*(2*j+2*r-1)^2)*
      ((1/(j+1)+1/r^2)*apexClosedRatio (j+r-1/2) r-
        jointlessTilt ((j+r-1/2)/(j+r)) (apexClosedRatio (j+r-1/2)) r)=
      apexPaymentReserve (j-1) (r-3/2) := by
  have h0 : r≠0 := by linarith
  have hm : r-1≠0 := by linarith
  have hp : r+1≠0 := by linarith
  have hp2 : r+2≠0 := by linarith
  have hj1 : j+1≠0 := by linarith
  have hsum : j+r≠0 := by linarith
  have hmu : j+r-1/2≠0 := by linarith
  unfold apexClosedRatio jointlessTilt apexPaymentReserve
  simp only [show r-1+1=r by ring,show r+1+1=r+2 by ring]
  have hnorm : -1+j*2+r*2≠0 := by linarith
  field_simp
  ring_nf
  field_simp [hnorm]
  ring

theorem apexClosedRatio_budget (j r : ℝ) (hj : 1≤j) (hr : 3/2≤r) :
    jointlessTilt ((j+r-1/2)/(j+r)) (apexClosedRatio (j+r-1/2)) r <
      (1/(j+1)+1/r^2)*apexClosedRatio (j+r-1/2) r := by
  have h := apexPaymentReserve_identity j r hj hr
  have hpos := apexPaymentReserve_pos (x:=j-1) (y:=r-3/2) (by linarith) (by linarith)
  have hd : 0<8*r^4*(j+1)*(j+r)*(r-1)^2*(r+1)^2*(r+2)*(2*j+2*r-1)^2 := by
    have hr0 : 0<r := by linarith
    have hm : 0<r-1 := by linarith
    have hp : 0<r+1 := by linarith
    have hp2 : 0<r+2 := by linarith
    have hj1 : 0<j+1 := by linarith
    have hs : 0<j+r := by linarith
    have hmu : 0<2*j+2*r-1 := by linarith
    positivity
  nlinarith

end Dowling
