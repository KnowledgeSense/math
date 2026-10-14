import MainTheorems.Laminar.BasisBlocks

namespace ResearchMain.Laminar

open Classical

theorem block_index_lt {k r : ℕ} (i : Fin k) (j : Fin r) : i.val * r + j.val < k * r := by
  have hi := Nat.mul_le_mul_right r (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at hi
  have hj := j.isLt
  omega

def blockIndex {k r : ℕ} (i : Fin k) (j : Fin r) : Fin (k * r) :=
  ⟨i.val * r + j.val, block_index_lt i j⟩

theorem rank_pos_of_index {k r : ℕ} (s : Fin (k * r)) : 0 < r := by
  by_contra h
  have hr : r = 0 := by omega
  have hs := s.isLt
  have hkr : k * r = 0 := by simp only [hr, Nat.mul_zero]
  omega

def indexRow {k r : ℕ} (s : Fin (k * r)) : Fin k :=
  ⟨s.val / r, (Nat.div_lt_iff_lt_mul (rank_pos_of_index s)).mpr s.isLt⟩

def indexColumn {k r : ℕ} (s : Fin (k * r)) : Fin r :=
  ⟨s.val % r, Nat.mod_lt _ (rank_pos_of_index s)⟩

theorem blockIndex_coordinates {k r : ℕ} (i : Fin k) (j : Fin r) :
    indexRow (blockIndex i j) = i ∧ indexColumn (blockIndex i j) = j := by
  have hr : 0 < r := by have := j.isLt; omega
  constructor
  · apply Fin.ext
    simp only [indexRow, blockIndex]
    rw [Nat.mul_comm i.val r, Nat.mul_add_div hr, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  · apply Fin.ext
    simp only [indexColumn, blockIndex]
    rw [Nat.mul_comm i.val r, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]

theorem blockIndex_row_column {k r : ℕ} (s : Fin (k * r)) :
    blockIndex (indexRow s) (indexColumn s) = s := by
  apply Fin.ext
  simpa only [blockIndex, indexRow, indexColumn, Nat.mul_comm] using Nat.div_add_mod s.val r

def cyclicIndex {N : ℕ} (s : Fin N) (j : ℕ) : Fin N :=
  ⟨(s.val + j) % N, Nat.mod_lt _ (by have := s.isLt; omega)⟩

theorem cyclic_shift_block {k r i t j : ℕ} (hi : i < k) (ht : t < r) (hj : j < r) :
    (i * r + t + j) % (k * r) =
      if t + j < r then i * r + (t + j) else ((i + 1) % k) * r + (t + j - r) := by
  have hib := Nat.mul_le_mul_right r (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hib
  by_cases hcarry : t + j < r
  · rw [ite_eq_left hcarry, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [ite_eq_right hcarry]
    by_cases hin : i + 1 < k
    · have hn := Nat.mul_le_mul_right r (Nat.succ_le_of_lt hin)
      rw [Nat.succ_mul, Nat.succ_mul] at hn
      rw [Nat.mod_eq_of_lt hin, Nat.mod_eq_of_lt (by omega), Nat.succ_mul]
      omega
    · have hie : i + 1 = k := by omega
      have hmul : i * r + r = k * r := by simpa only [Nat.succ_mul] using congrArg (fun a => a * r) hie
      have hrem : t + j - r < k * r := by omega
      have hsum : i * r + t + j = k * r + (t + j - r) := by omega
      rw [hie, Nat.mod_self, Nat.zero_mul, Nat.zero_add, hsum, Nat.add_mod,
        Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hrem]
      exact Nat.mod_eq_of_lt hrem

theorem cyclicIndex_block {k r : ℕ} (i : Fin k) (t : Fin r) (j : Fin r) :
    cyclicIndex (blockIndex i t) j.val =
      if h : t.val + j.val < r then blockIndex i ⟨t.val + j.val, h⟩
      else blockIndex (nextRow i) ⟨t.val + j.val - r, by have := t.isLt; have := j.isLt; omega⟩ := by
  apply Fin.ext
  simp only [cyclicIndex, blockIndex]
  rw [cyclic_shift_block i.isLt t.isLt j.isLt]
  split <;> rfl

end ResearchMain.Laminar
