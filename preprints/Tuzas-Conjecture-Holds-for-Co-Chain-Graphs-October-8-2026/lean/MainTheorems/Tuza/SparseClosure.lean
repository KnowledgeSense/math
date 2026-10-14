import MainTheorems.Tuza.SparseChecks.Orders01To10
import MainTheorems.Tuza.SparseChecks.Orders11To20
import MainTheorems.Tuza.SparseChecks.Orders21To30
import MainTheorems.Tuza.SparseChecks.Orders31To40
import MainTheorems.Tuza.SparseChecks.Orders41To50
import MainTheorems.Tuza.SparseChecks.Orders51To55

namespace ResearchMain.Tuza.FerrersProfile

theorem sparse_bounded_inequality {a b : ℕ} (d : FerrersProfile a b)
    (ha : 0 < a) (hab : a ≤ b) (hn : a + b ≤ 110)
    (hs : d.height (halfUp b) < halfUp a)
    (hq : 3 * ((halfUp a) ^ 2 + (halfUp b) ^ 2) < 84 * (halfUp a + halfUp b)) :
    Inequality d.graph := by
  have ha55 : a ≤ 55 := by omega
  interval_cases a
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_1
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_2
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_3
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_4
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_5
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_6
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_7
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_8
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_9
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_10
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_11
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_12
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_13
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_14
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_15
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_16
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_17
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_18
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_19
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_20
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_21
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_22
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_23
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_24
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_25
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_26
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_27
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_28
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_29
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_30
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_31
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_32
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_33
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_34
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_35
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_36
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_37
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_38
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_39
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_40
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_41
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_42
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_43
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_44
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_45
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_46
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_47
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_48
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_49
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_50
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_51
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_52
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_53
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_54
  · exact d.sparseSizeTest_sound ha hab hn hs hq sparseChecked_55

theorem sparse_oriented_inequality {a b : ℕ} (d : FerrersProfile a b)
    (ha : 0 < a) (hab : a ≤ b) (hs : d.height (halfUp b) < halfUp a) : Inequality d.graph := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  by_cases hl : 84 * (halfUp a + halfUp b) ≤ 3 * ((halfUp a) ^ 2 + (halfUp b) ^ 2)
  · exact d.sparse_large_inequality ha hb hs hl
  · by_cases hn : 111 ≤ a + b
    · exact d.sparse_unbounded_reduction ha hb hs hn
    · exact d.sparse_bounded_inequality ha hab (by omega) hs (by omega)

theorem sparse_inequality {a b : ℕ} (d : FerrersProfile a b)
    (ha : 0 < a) (hb : 0 < b) (hs : d.height (halfUp b) < halfUp a) : Inequality d.graph := by
  by_cases hab : a ≤ b
  · exact d.sparse_oriented_inequality ha hab hs
  · have hts : d.transpose.height (halfUp a) < halfUp b := by
      rw [d.transpose_median_height ha]
      exact (d.median_sparse_iff ha).mp hs
    exact (inequality_iso d.transposeIso).mp
      (d.transpose.sparse_oriented_inequality hb (by omega) hts)

end ResearchMain.Tuza.FerrersProfile
