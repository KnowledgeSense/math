import Dowling.FullInvariantUniqueness
import Dowling.DowlingCandidateReciprocity
import Dowling.DowlingCandidateZRelation

noncomputable section
namespace Dowling
open PowerSeries
variable {G : Type*} [Group G] [Fintype G]

/-- The original full-Dowling KL and Z generating series are the explicit
inverse-log candidates, proved from actual flats rather than assumed as input. -/
theorem full_candidates_identification :
    fullPSeries G = dowlingPCandidate (Fintype.card G) ∧
      fullZSeries G = dowlingZCandidate (Fintype.card G) := by
  apply full_invariants_unique
  · simpa only [coeff_zero_eq_constantCoeff_apply] using dowlingPCandidate_constantCoeff (Fintype.card G)
  · exact fun n hn k hk => dowlingPCandidate_high_coeff (Fintype.card G) n k hn hk
  · exact fun n t ht => dowlingZCandidate_eval_reciprocal (Fintype.card G) t ht n
  · apply dowlingCandidate_flat_relation
    exact_mod_cast Fintype.card_ne_zero (α := G)

theorem fullPSeries_eq_candidate : fullPSeries G = dowlingPCandidate (Fintype.card G) :=
  full_candidates_identification.1

theorem fullZSeries_eq_candidate : fullZSeries G = dowlingZCandidate (Fintype.card G) :=
  full_candidates_identification.2

end Dowling
