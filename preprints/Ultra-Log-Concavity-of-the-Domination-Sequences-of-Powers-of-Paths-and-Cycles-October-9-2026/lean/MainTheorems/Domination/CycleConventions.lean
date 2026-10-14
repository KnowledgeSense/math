import MainTheorems.Domination.Powers

namespace ResearchMain.Domination

theorem fin_sub_value {n : ℕ} (a b : Fin n) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else n + a.val - b.val := by
  by_cases h : b.val ≤ a.val
  · rw [ite_eq_left h]
    exact Fin.sub_val_of_le h
  · rw [ite_eq_right h]
    exact Fin.coe_sub_iff_lt.mpr (by change a.val < b.val; omega)

theorem cyclePower_one (n : ℕ) : cyclePower n 1 = SimpleGraph.cycleGraph n := by
  ext u v
  rw [SimpleGraph.cycleGraph_adj', fin_sub_value, fin_sub_value]
  change (u ≠ v ∧ (Nat.dist u.val v.val ≤ 1 ∨ n - Nat.dist u.val v.val ≤ 1)) ↔ _
  have hne : u ≠ v ↔ u.val ≠ v.val := not_congr Fin.ext_iff
  rw [hne]
  unfold Nat.dist
  have hu := u.isLt
  have hv := v.isLt
  split_ifs <;> omega

end ResearchMain.Domination
