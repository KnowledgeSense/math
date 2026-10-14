import MainTheorems.Tuza.HalfQuasigroup

namespace ResearchMain.Tuza

def parityEquiv (m : ℕ) : Fin (2 * m) ≃ Fin m × Bool where
  toFun z := (⟨z.val / 2, by have hz := z.isLt; omega⟩, decide (z.val % 2 = 1))
  invFun x := ⟨2 * x.1.val + if x.2 then 1 else 0, by
    obtain ⟨i, b⟩ := x
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals have hi := i.isLt; omega⟩
  left_inv z := by
    apply Fin.ext
    dsimp
    by_cases hz : z.val % 2 = 1
    · simp only [hz, decide_true, ite_true]
      omega
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      omega
  right_inv x := by
    obtain ⟨i, b⟩ := x
    apply Prod.ext
    · apply Fin.ext
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      all_goals omega
    · cases b <;> simp [Nat.add_mod]

def halfLabelEquiv (m : ℕ) : Fin m × Bool ≃ Fin (2 * m) where
  toFun x := ⟨x.1.val + if x.2 then m else 0, by
    obtain ⟨i, b⟩ := x
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals have hi := i.isLt; omega⟩
  invFun z := (⟨if z.val < m then z.val else z.val - m, by
    have hz := z.isLt
    split_ifs <;> omega⟩, decide (m ≤ z.val))
  left_inv x := by
    obtain ⟨i, b⟩ := x
    apply Prod.ext
    · apply Fin.ext
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      all_goals split_ifs <;> have hi := i.isLt <;> omega
    · cases b <;> simp [Nat.not_le_of_lt i.isLt]
  right_inv z := by
    apply Fin.ext
    dsimp
    by_cases hz : z.val < m
    · simp [hz, Nat.not_le_of_lt hz]
    · simp [hz, Nat.le_of_not_gt hz]

end ResearchMain.Tuza
