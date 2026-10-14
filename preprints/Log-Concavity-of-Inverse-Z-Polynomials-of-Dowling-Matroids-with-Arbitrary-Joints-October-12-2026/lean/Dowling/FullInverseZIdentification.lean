import Dowling.FullInverseZGeneratingFunction
import Dowling.DowlingInverseZCandidateUniqueness
import Dowling.DowlingInverseZCandidateCoefficients

noncomputable section
namespace Dowling
open PowerSeries
variable {G : Type*} [Group G] [Fintype G]

/-- The original full-Dowling inverse-Z invariant equals the explicit Lambert
candidate, with every characterization premise supplied by actual flats. -/
theorem fullYSeries_eq_candidate :
    fullYSeries G=dowlingInverseZCandidate (Fintype.card G) := by
  apply dowlingInverseZCandidate_unique
  · exact_mod_cast Fintype.card_ne_zero (α := G)
  · rw [← fullZSeries_eq_candidate]
    exact fullYSeries_flat_relation

/-- Exact finite coefficient formula for the genuine full-Dowling inverse-Z
polynomial. The scalar definition includes zero above rank. -/
theorem fullY_coeff_real (n k : ℕ) :
    ((fullY G n).coeff k : ℝ) = (n.factorial : ℝ)*(Fintype.card G : ℝ)^n*
      dowlingScalarCoefficient (Fintype.card G : ℝ)⁻¹ n k := by
  have he := congrArg (fun f : PowerSeries (Polynomial ℝ) => (coeff n f).coeff k)
    (fullYSeries_eq_candidate (G := G))
  rw [dowlingInverseZCandidate_coeff_coeff] at he
  rw [fullYSeries,invariantEGF_coeff] at he
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_map] at he
  change (n.factorial : ℝ)⁻¹*((fullY G n).coeff k : ℝ)=_ at he
  have hn : (n.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  calc
    _ = (n.factorial : ℝ)*((n.factorial : ℝ)⁻¹*((fullY G n).coeff k : ℝ)) := by
      rw [← mul_assoc,mul_inv_cancel₀ hn,one_mul]
    _ = _ := by rw [he]; ring

end Dowling
