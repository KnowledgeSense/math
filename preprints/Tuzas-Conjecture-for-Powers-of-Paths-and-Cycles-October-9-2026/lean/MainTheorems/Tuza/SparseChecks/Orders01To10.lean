import MainTheorems.Tuza.SparseFiniteTest

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace ResearchMain.Tuza

theorem sparseChecked_1 : sparseSizeTest 1 = true := by decide +kernel

theorem sparseChecked_2 : sparseSizeTest 2 = true := by decide +kernel

theorem sparseChecked_3 : sparseSizeTest 3 = true := by decide +kernel

theorem sparseChecked_4 : sparseSizeTest 4 = true := by decide +kernel

theorem sparseChecked_5 : sparseSizeTest 5 = true := by decide +kernel

theorem sparseChecked_6 : sparseSizeTest 6 = true := by decide +kernel

theorem sparseChecked_7 : sparseSizeTest 7 = true := by decide +kernel

theorem sparseChecked_8 : sparseSizeTest 8 = true := by decide +kernel

theorem sparseChecked_9 : sparseSizeTest 9 = true := by decide +kernel

theorem sparseChecked_10 : sparseSizeTest 10 = true := by decide +kernel

end ResearchMain.Tuza
