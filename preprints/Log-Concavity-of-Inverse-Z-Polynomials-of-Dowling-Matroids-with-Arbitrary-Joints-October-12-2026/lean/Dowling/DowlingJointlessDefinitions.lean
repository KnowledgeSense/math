import Dowling.DowlingRetainedPayment

noncomputable section
namespace Dowling

/-- The exact rational correction polynomial from the jointless fixed-total kernel. -/
def jointlessCorrection (a μ r : ℝ) : ℝ :=
  a^2*r^3/3+(a^2-(a-a^2/3)*μ)*r^2+
    ((2*a-2*a^2/3)*μ^2-2*a^2*μ+a^2/6)*r+
    a*(1-a)*μ/4-a^2/2+a^2*(3*r-2*μ)/(16*r*(r+1))

def jointlessRatioFunction (a μ r : ℝ) : ℝ := jointlessCorrection a μ r/r

/-- Universal natural-power form, retaining the two initial weights without negative exponents. -/
def jointlessNormalizedWeight (a μ : ℝ) (j : ℕ) : ℝ :=
  1-(μ/(μ+1/2))^j*(μ+1/2)^2/μ^4*
    jointlessRatioFunction a μ (μ+1/2-j)

/-- The positive full-Dowling raised weight, with its original fixed total degree. -/
def dowlingBaseWeight (a : ℝ) (n j : ℕ) : ℝ :=
  a/(n+a)*dowlingQuadraticWeight ((n+a)/2) j

def jointlessWeight (a : ℝ) (n j : ℕ) : ℝ :=
  dowlingBaseWeight a n j*jointlessNormalizedWeight a ((n+a-1)/2) j

def retainedNontrivialWeight (a θ : ℝ) (n j : ℕ) : ℝ :=
  dowlingBaseWeight a n j*(1-θ+θ*jointlessNormalizedWeight a ((n+a-1)/2) j)

/-- Literal unraised coefficient in the exact corrected homogeneous kernel. -/
def jointlessUnraisedWeight (a : ℝ) (n j : ℕ) : ℝ :=
  dowlingQuadraticWeight ((n+a)/2) j-
    (a*n/(n+a-1))*dowlingQuadraticWeight ((n+a-1)/2) j-
    (if j=0 then 0 else a*(1-a)*dowlingQuadraticWeight ((n+a-1)/2) (j-1))-
    (if j<2 then 0 else (a^2/3)*dowlingQuadraticWeight ((n+a-1)/2) (j-2))

/-- Literal fixed-total exponent-raising difference. Its equality to the closed weight is separate. -/
def jointlessRaisedWeight (a : ℝ) (n j : ℕ) : ℝ :=
  a/2*(jointlessUnraisedWeight a n j/((n+a)/2-j)-
    if j=0 then 0 else jointlessUnraisedWeight a n (j-1)/((n+a)/2-j+1))

end Dowling
