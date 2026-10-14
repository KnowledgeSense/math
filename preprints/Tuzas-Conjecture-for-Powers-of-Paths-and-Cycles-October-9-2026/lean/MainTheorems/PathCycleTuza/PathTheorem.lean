import MainTheorems.Tuza.Classification
import MainTheorems.PathCycleTuza.PathLarge
import MainTheorems.PathCycleTuza.ConsecutivePath
import MainTheorems.PathCycleTuza.BoundaryPath
import MainTheorems.PathCycleTuza.SixPath

namespace ResearchMain.PathCycleTuza

open Tuza

theorem path_inequality (n k : ℕ) : Inequality (pathPower n k) := by
  by_cases hn : n ≤ 2 * k + 2
  · exact coChain_inequality _ (pathPower_short_isCoChain n k hn)
  by_cases hk : k ≤ 6
  · interval_cases k
    · exact path_zero_inequality n
    · exact path_one_inequality n
    · exact path_two_inequality n
    · exact path_three_to_five n 3 (by decide) (by decide)
    · exact path_three_to_five n 4 (by decide) (by decide)
    · exact path_three_to_five n 5 (by decide) (by decide)
    · exact path_six_inequality n
  by_cases he₈ : k = 8
  · exact path_eight_or_nine n k (Or.inl he₈)
  by_cases he₉ : k = 9
  · exact path_eight_or_nine n k (Or.inr he₉)
  exact path_large_inequality n k (by omega) (by omega) he₈ he₉

end ResearchMain.PathCycleTuza
