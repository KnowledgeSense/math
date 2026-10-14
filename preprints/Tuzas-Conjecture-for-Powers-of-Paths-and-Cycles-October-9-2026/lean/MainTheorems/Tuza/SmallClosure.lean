import MainTheorems.Tuza.SmallChecks.One
import MainTheorems.Tuza.SmallChecks.Two
import MainTheorems.Tuza.SmallChecks.Three
import MainTheorems.Tuza.SmallChecks.Four
import MainTheorems.Tuza.SmallChecks.Five
import MainTheorems.Tuza.SmallChecks.Six

namespace ResearchMain.Tuza.FerrersProfile

theorem small_inequality {a b : ℕ} (d : FerrersProfile a b)
    (ha : 0 < a) (hab : a ≤ b) (hn : a + b ≤ 12) : Inequality d.graph := by
  have ha6 : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by omega
  have hbmax : b ≤ 12 - a := by omega
  rcases ha6 with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals interval_cases b
  · exact checked_profiles_sound d _ smallChecked_1_1
  · exact checked_profiles_sound d _ smallChecked_1_2
  · exact checked_profiles_sound d _ smallChecked_1_3
  · exact checked_profiles_sound d _ smallChecked_1_4
  · exact checked_profiles_sound d _ smallChecked_1_5
  · exact checked_profiles_sound d _ smallChecked_1_6
  · exact checked_profiles_sound d _ smallChecked_1_7
  · exact checked_profiles_sound d _ smallChecked_1_8
  · exact checked_profiles_sound d _ smallChecked_1_9
  · exact checked_profiles_sound d _ smallChecked_1_10
  · exact checked_profiles_sound d _ smallChecked_1_11
  · exact checked_profiles_sound d _ smallChecked_2_2
  · exact checked_profiles_sound d _ smallChecked_2_3
  · exact checked_profiles_sound d _ smallChecked_2_4
  · exact checked_profiles_sound d _ smallChecked_2_5
  · exact checked_profiles_sound d _ smallChecked_2_6
  · exact checked_profiles_sound d _ smallChecked_2_7
  · exact checked_profiles_sound d _ smallChecked_2_8
  · exact checked_profiles_sound d _ smallChecked_2_9
  · exact checked_profiles_sound d _ smallChecked_2_10
  · exact checked_profiles_sound d _ smallChecked_3_3
  · exact checked_profiles_sound d _ smallChecked_3_4
  · exact checked_profiles_sound d _ smallChecked_3_5
  · exact checked_profiles_sound d _ smallChecked_3_6
  · exact checked_profiles_sound d _ smallChecked_3_7
  · exact checked_profiles_sound d _ smallChecked_3_8
  · exact checked_profiles_sound d _ smallChecked_3_9
  · exact checked_profiles_sound d _ smallChecked_4_4
  · exact checked_profiles_sound d _ smallChecked_4_5
  · exact checked_profiles_sound d _ smallChecked_4_6
  · exact checked_profiles_sound d _ smallChecked_4_7
  · exact checked_profiles_sound d _ smallChecked_4_8
  · exact checked_profiles_sound d _ smallChecked_5_5
  · exact checked_profiles_sound d _ smallChecked_5_6
  · exact checked_profiles_sound d _ smallChecked_5_7
  · exact checked_profiles_sound d _ smallChecked_6_6

end ResearchMain.Tuza.FerrersProfile
