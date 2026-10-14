import MainTheorems.Tuza.DenseFiniteTest

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

namespace ResearchMain.Tuza

theorem denseChecked_1 : denseSizeTest 1 = true := by decide +kernel

theorem denseChecked_2 : denseSizeTest 2 = true := by decide +kernel

theorem denseChecked_3 : denseSizeTest 3 = true := by decide +kernel

theorem denseChecked_4 : denseSizeTest 4 = true := by decide +kernel

theorem denseChecked_5 : denseSizeTest 5 = true := by decide +kernel

theorem denseChecked_6 : denseSizeTest 6 = true := by decide +kernel

theorem denseChecked_7 : denseSizeTest 7 = true := by decide +kernel

theorem denseChecked_8 : denseSizeTest 8 = true := by decide +kernel

theorem denseChecked_9 : denseSizeTest 9 = true := by decide +kernel

theorem denseChecked_10 : denseSizeTest 10 = true := by decide +kernel

end ResearchMain.Tuza
