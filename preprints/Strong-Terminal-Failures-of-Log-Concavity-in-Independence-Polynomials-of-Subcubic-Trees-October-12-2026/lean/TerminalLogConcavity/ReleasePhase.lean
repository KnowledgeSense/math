import TerminalLogConcavity.PhaseProduct
import TerminalLogConcavity.ChainUpper
import TerminalLogConcavity.ReleaseLower

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

theorem lowerChain_product_bound {q : ℕ} (hq : 2 ≤ q) (t : ℕ)
    (ha : 128 * q ^ 4 ≤ amplifier t) :
    RealCoeffLE (realPolynomial (∏ i ∈ Finset.range q, lowerChain q t (i + 1)))
      (C 2 * realPolynomial (scaledGaussianPolynomial q (amplifier t))) := by
  have h := natural_phase_product_bound (by omega : 1 ≤ q)
    (fun i => lowerChain q t (i + 1)) (fun i => chainPhasePolynomial q t (i + 1))
    (fun i hi j => lowerChain_phase_scaled hq t (i + 1) j ha (by omega))
  rw [phase_product_eq_scaledGaussian] at h
  exact h

end TerminalLogConcavity
