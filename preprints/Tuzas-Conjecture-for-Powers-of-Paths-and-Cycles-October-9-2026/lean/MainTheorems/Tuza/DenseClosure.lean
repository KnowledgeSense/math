import MainTheorems.Tuza.DenseChecks.Orders01To10
import MainTheorems.Tuza.DenseChecks.Orders11To20
import MainTheorems.Tuza.DenseChecks.Orders21To30
import MainTheorems.Tuza.DenseChecks.Orders31To40
import MainTheorems.Tuza.DenseChecks.Orders41To50
import MainTheorems.Tuza.DenseChecks.Orders51To60
import MainTheorems.Tuza.DenseChecks.Orders61To70
import MainTheorems.Tuza.DenseChecks.Orders71To80
import MainTheorems.Tuza.DenseChecks.Orders81To86

namespace ResearchMain.Tuza.FerrersProfile

theorem dense_bounded_inequality {a b : ℕ} (d : FerrersProfile a b)
    (ha : 0 < a) (hab : a ≤ b) (hd : halfUp a ≤ d.height (halfUp b))
    (hn : halfUp a + halfUp b < 88) : Inequality d.graph := by
  have ha86 : a ≤ 86 := by unfold halfUp at hn; omega
  interval_cases a
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_1
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_2
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_3
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_4
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_5
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_6
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_7
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_8
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_9
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_10
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_11
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_12
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_13
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_14
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_15
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_16
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_17
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_18
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_19
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_20
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_21
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_22
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_23
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_24
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_25
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_26
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_27
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_28
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_29
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_30
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_31
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_32
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_33
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_34
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_35
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_36
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_37
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_38
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_39
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_40
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_41
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_42
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_43
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_44
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_45
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_46
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_47
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_48
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_49
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_50
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_51
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_52
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_53
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_54
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_55
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_56
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_57
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_58
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_59
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_60
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_61
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_62
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_63
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_64
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_65
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_66
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_67
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_68
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_69
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_70
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_71
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_72
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_73
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_74
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_75
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_76
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_77
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_78
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_79
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_80
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_81
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_82
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_83
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_84
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_85
  · exact d.denseSizeTest_sound ha hab hd hn denseChecked_86

theorem dense_oriented_inequality {a b : ℕ} (d : FerrersProfile a b)
    (ha : 0 < a) (hab : a ≤ b) (hd : halfUp a ≤ d.height (halfUp b)) : Inequality d.graph := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  by_cases hn : 88 ≤ halfUp a + halfUp b
  · exact d.dense_large_inequality ha hb hd hn
  · exact d.dense_bounded_inequality ha hab hd (by omega)

theorem dense_inequality {a b : ℕ} (d : FerrersProfile a b)
    (ha : 0 < a) (hb : 0 < b) (hd : halfUp a ≤ d.height (halfUp b)) : Inequality d.graph := by
  by_cases hab : a ≤ b
  · exact d.dense_oriented_inequality ha hab hd
  · have htd : halfUp b ≤ d.transpose.height (halfUp a) := by
      rw [d.transpose_median_height ha]
      exact d.median_dense_degree ha hd
    exact (inequality_iso d.transposeIso).mp
      (d.transpose.dense_oriented_inequality hb (by omega) htd)

end ResearchMain.Tuza.FerrersProfile
