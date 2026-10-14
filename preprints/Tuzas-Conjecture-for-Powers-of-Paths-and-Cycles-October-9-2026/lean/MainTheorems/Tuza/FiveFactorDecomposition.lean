import MainTheorems.Tuza.FiveFactorGadgets
import MainTheorems.Tuza.OneFactorInflation
import MainTheorems.Tuza.DeletedFiniteFactors
import MainTheorems.Tuza.SkolemDecomposition

namespace ResearchMain.Tuza

theorem five_factor_decomposition (m : ℕ) :
    Nonempty (FactorDecomposition (Fin (6 * m)) (Fin 5)) := by
  classical
  let q := m / 6
  have hm : m = 6 * q + m % 6 := by omega
  have hr : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by omega
  rcases hr with hr | hr | hr | hr | hr | hr
  · obtain ⟨S⟩ := exists_steinerOperation_one q
    have he : 6 * q + 1 = m + 1 := by omega
    rw [he] at S
    obtain ⟨D⟩ := deleted_one_factor m S
    obtain ⟨E⟩ := five_factor_two_six
    obtain ⟨T⟩ := inflate_one_factor_decomposition D E
    exact T.toFinite (6 * m) 5 (by simp [Nat.mul_comm]) (by simp)
  · obtain ⟨D⟩ := exists_complete_decomposition_one q
    have he : 6 * q + 1 = m := by omega
    rw [he] at D
    obtain ⟨E⟩ := five_factor_six
    obtain ⟨T⟩ := inflate_complete_decomposition D E
    exact T.toFinite (6 * m) 5 (by simp [Nat.mul_comm]) (by simp)
  · obtain ⟨S⟩ := exists_steinerOperation_three q
    have he : 6 * q + 3 = m + 1 := by omega
    rw [he] at S
    obtain ⟨D⟩ := deleted_one_factor m S
    obtain ⟨E⟩ := five_factor_two_six
    obtain ⟨T⟩ := inflate_one_factor_decomposition D E
    exact T.toFinite (6 * m) 5 (by simp [Nat.mul_comm]) (by simp)
  · obtain ⟨D⟩ := exists_complete_decomposition_three q
    have he : 6 * q + 3 = m := by omega
    rw [he] at D
    obtain ⟨E⟩ := five_factor_six
    obtain ⟨T⟩ := inflate_complete_decomposition D E
    exact T.toFinite (6 * m) 5 (by simp [Nat.mul_comm]) (by simp)
  · obtain ⟨S⟩ := exists_steinerOperation_three (2 * q + 1)
    have he : 6 * (2 * q + 1) + 3 = 2 * m + 1 := by omega
    rw [he] at S
    obtain ⟨D⟩ := deleted_one_factor (2 * m) S
    obtain ⟨E⟩ := five_factor_two_three
    obtain ⟨T⟩ := inflate_one_factor_decomposition D E
    exact T.toFinite (6 * m) 5 (by simp; omega) (by simp)
  · obtain ⟨S⟩ := exists_steinerOperation_one (2 * q + 2)
    have he : 6 * (2 * q + 2) + 1 = 2 * m + 3 := by omega
    rw [he] at S
    obtain ⟨D⟩ := deleted_three_factors (2 * m) S
    obtain ⟨T⟩ := inflate_three_factor_decomposition D
    exact T.toFinite (6 * m) 5 (by simp; omega) (by simp)

end ResearchMain.Tuza
