import WeakClergyman.Counting

namespace WeakClergyman.AntiRecurrence

variable {k : ℕ} {a : Fin k → ℕ} (S : AntiRecurrence k a)
variable (hk : 2 ≤ k) (ha : ∀ j, 0 < a j)
include hk ha

 theorem forward_position (n : ℕ) : S.B (k*n + (k-1)) < S.A n := by
  classical
  let last : Fin k := ⟨k-1, by omega⟩
  let first : Fin k := ⟨0, by omega⟩
  have hd : first ≠ last := by
    intro h
    have := congrArg Fin.val h
    dsimp [first, last] at this
    omega
  have hh : a last * S.B (k*n+last.val) < ∑ j : Fin k, a j * S.B (k*n+j.val) :=
    Finset.single_lt_sum (f := fun j : Fin k => a j * S.B (k*n+j.val)) hd (Finset.mem_univ _) (Finset.mem_univ _)
      (Nat.mul_pos (ha first) (S.B_pos _)) (fun _ _ _ => Nat.zero_le _)
  rw [S.recurrence]
  apply lt_of_le_of_lt ?_ hh
  dsimp [last]
  exact Nat.le_mul_of_pos_left _ (ha last)

omit hk ha in
 theorem separation (n : ℕ) :
    S.A n + k * (∑ j : Fin k, a j) ≤ S.A (n+1) := by
  classical
  rw [S.recurrence n, S.recurrence (n+1), Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have h := S.B_strictMono.add_le_nat k (k*n+j.val)
  have he : k + (k*n+j.val) = k*(n+1)+j.val := by ring
  rw [he] at h
  nlinarith

omit hk in
 theorem tau_lower : k ≤ ∑ j : Fin k, a j := by
  calc
    k = ∑ _j : Fin k, 1 := by simp
    _ ≤ ∑ j : Fin k, a j := Finset.sum_le_sum fun j _ => ha j

 theorem first_block (j : Fin k) : S.B j.val = j.val+1 := by
  have hf := S.forward_position hk ha 0
  have hba : S.B j.val < S.A 0 := by
    apply lt_of_le_of_lt (S.B_strictMono.monotone ?_) hf
    simp only [Nat.mul_zero, Nat.zero_add]
    omega
  have hz : (valuesBelow S.A (S.B j.val)).card = 0 := by
    have hc := card_valuesBelow_le S.A_strictMono hba.le
    omega
  have hr := S.complementary_rank j.val
  omega

 theorem initial_value : S.A 0 = ∑ j : Fin k, a j * (j.val+1) := by
  rw [S.recurrence]
  apply Finset.sum_congr rfl
  intro j _
  simp [S.first_block hk ha j]

 theorem initial_bounds : (∑ j : Fin k, a j) ≤ S.A 0 ∧
    S.A 0 ≤ k * (∑ j : Fin k, a j) := by
  rw [S.initial_value hk ha]
  constructor
  · exact Finset.sum_le_sum fun j _ => Nat.le_mul_of_pos_right _ (by omega)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have := j.isLt
    nlinarith

end WeakClergyman.AntiRecurrence
