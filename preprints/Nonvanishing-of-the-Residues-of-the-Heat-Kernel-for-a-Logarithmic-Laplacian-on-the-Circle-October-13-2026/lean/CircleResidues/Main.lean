import CircleResidues.SourceBridge
import CircleResidues.BellNormalization

noncomputable section
open Finset
namespace CircleResidues

/-- Whole nonvanishing theorem in the original ordinary partial Bell normalization. -/
theorem ordinaryBell_residue_nonzero (m : ℕ) :
    (∑ ell ∈ range (2 * m + 1),
      (-((1 : ℚ) / 2 - m)) ^ ell / (ell.factorial : ℚ) * ordinaryBell (2 * m) ell) ≠ 0 := by
  rw [← residuePolynomial_eq_bell_sum]
  exact residuePolynomial_ne_zero m

/-- Exact two-adic valuation, including the already-known zeroth pole. -/
theorem ordinaryBell_residue_valuation (m : ℕ) :
    padicValRat 2 (∑ ell ∈ range (2 * m + 1),
      (-((1 : ℚ) / 2 - m)) ^ ell / (ell.factorial : ℚ) * ordinaryBell (2 * m) ell) =
      -3 * (m : ℤ) - padicValNat 2 m.factorial := by
  rw [← residuePolynomial_eq_bell_sum]
  exact (residuePolynomial_valuation m).2

end CircleResidues
