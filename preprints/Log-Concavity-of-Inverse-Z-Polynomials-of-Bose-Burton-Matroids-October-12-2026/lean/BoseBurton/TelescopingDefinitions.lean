import BoseBurton.ScalarDefinitions

noncomputable section
namespace BoseBurton

def cancellationWeight (z : ℝ) (r s j : ℕ) : ℝ :=
  z^(j*(r-s+j-1))*gaussian z s j*qFactorial z (r-j)/
    (qFactorial z r*qFactorial z j)

def cancellationBracket (z : ℝ) (r h k : ℕ) : ℝ :=
  1-2*z^h-z^r+z^h*(z^k+z^(r-k))

end BoseBurton
