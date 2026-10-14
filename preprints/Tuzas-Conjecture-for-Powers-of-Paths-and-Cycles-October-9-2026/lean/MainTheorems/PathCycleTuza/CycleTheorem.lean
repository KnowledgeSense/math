import MainTheorems.PathCycleTuza.CycleLarge
import MainTheorems.PathCycleTuza.ConsecutiveCycle
import MainTheorems.PathCycleTuza.EvenSixCycle
import MainTheorems.PathCycleTuza.OddSixCycle

namespace ResearchMain.PathCycleTuza

open Tuza

theorem cycle_six_inequality (n : ℕ) : Inequality (cyclePower n 6) := by
  by_cases hn : n ≤ 13
  · rw [cyclePower_complete n 6 (by omega)]
    exact complete_inequality n
  · by_cases he : n % 2 = 0
    · have hp := evenSixCycle_bound n (by omega) he
      have hc := cycle_run_cover n 6 (by decide) (by omega)
      norm_num at hc
      exact hc.trans hp
    · have hp := oddSixCycle_bound n (by omega) (by omega)
      have hc := cycle_run_cover_even_odd n 6 (by decide) (by omega) (by decide) (by omega)
      norm_num at hc
      unfold Inequality
      omega

theorem cycle_inequality (n k : ℕ) : Inequality (cyclePower n k) := by
  by_cases hn : n ≤ 2 * k + 1
  · rw [cyclePower_complete n k hn]
    exact complete_inequality n
  by_cases hk : k ≤ 6
  · interval_cases k
    · exact cycle_zero_inequality n
    · exact cycle_one_inequality n
    · exact cycle_two_inequality n
    · exact cycle_three_to_five n 3 (by decide) (by decide)
    · exact cycle_three_to_five n 4 (by decide) (by decide)
    · exact cycle_three_to_five n 5 (by decide) (by decide)
    · exact cycle_six_inequality n
  exact cycle_large_inequality n k (by omega) (by omega)

end ResearchMain.PathCycleTuza
