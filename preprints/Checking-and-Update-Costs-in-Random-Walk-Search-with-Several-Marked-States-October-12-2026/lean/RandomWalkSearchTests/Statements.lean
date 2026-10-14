import RandomWalkSearch

open RandomWalkSearch RandomWalkSearch.Cycle
open scoped ENNReal

#check free_restoration_main
#check consecutive_main
#check endpoints_main
#check no_uniform_split_main
#check marked_mass_real_exact
#check Randomized.MeasurableCoordinates.observable
#check Canonical.algorithm_observable
#check Canonical.setup_independent_tape
#check Canonical.tape_independent

local instance : NeZero (N 2) := ⟨by norm_num [N]⟩
local instance : NeZero (L 2) := ⟨by norm_num [L]⟩

/-- A concrete small instance checks nonvacuity of all four endpoint witnesses. -/
example : ∃ pRS pRD pCS pCD : Policy (Vertex 2),
    IsRestorationEndpoint pRS (4*((L 2-1:ℕ):ℝ)) (L 2) ∧
    IsRestorationEndpoint pRD (4*((N 2-1:ℕ):ℝ)) 2 ∧
    IsConsecutiveEndpoint pCS (2*(L 2:ℝ)^2) (L 2) ∧
    IsConsecutiveEndpoint pCD (2*(N 2:ℝ)^2) 2 :=
  four_endpoints (by decide)

example : L 2 = 4 ∧ N 2 = 256 := by norm_num [L,N]

/-- The large-instance premise of the universal theorems is satisfiable. -/
example : 16 * (1 + 1) ≤ (32 : ℕ) := by decide
