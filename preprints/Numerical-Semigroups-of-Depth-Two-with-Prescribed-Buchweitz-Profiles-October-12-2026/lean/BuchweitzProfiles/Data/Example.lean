import BuchweitzProfiles.Sumsets

namespace BuchweitzProfiles

/-- The finite seed of the genus-172 example. -/
def exampleC : Finset Nat := {0, 26, 28, 97}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma example_stable :
    (sumset exampleC 7).filter (· < 169) = (sumset exampleC 6).filter (· < 169) := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma example_six_count : truncatedCount exampleC 169 6 = 34 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma example_small_counts :
    truncatedCount exampleC 169 1 = 4 ∧
    truncatedCount exampleC 169 2 = 9 ∧
    truncatedCount exampleC 169 3 = 16 ∧
    truncatedCount exampleC 169 4 = 21 ∧
    truncatedCount exampleC 169 5 = 27 := by decide

end BuchweitzProfiles
