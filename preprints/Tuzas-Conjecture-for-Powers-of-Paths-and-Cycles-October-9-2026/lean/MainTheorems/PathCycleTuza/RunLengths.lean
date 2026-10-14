import MainTheorems.PathCycleTuza.Basic

namespace ResearchMain.PathCycleTuza

theorem fill_sum (h R r : ℕ) :
    (∑ i : Fin r, min h (R - h * i.val)) = min R (h * r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Nat.mul_succ]
    omega

def runCount (n k : ℕ) : ℕ := 2 * (n / (2 * Tuza.halfUp k))

def runRemainder (n k : ℕ) : ℕ := n - runCount n k * Tuza.halfUp k

def runLength (n k : ℕ) (i : Fin (runCount n k)) : ℕ :=
  Tuza.halfUp k + min (k / 2) (runRemainder n k - k / 2 * i.val)

theorem runCount_even (n k : ℕ) : runCount n k % 2 = 0 := by
  unfold runCount
  omega

theorem halfUp_split (k : ℕ) : Tuza.halfUp k + k / 2 = k := by
  unfold Tuza.halfUp
  omega

theorem runCount_four (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 2 ≤ n) :
    4 ≤ runCount n k := by
  have hp := Tuza.halfUp_pos (by omega : 0 < k)
  have hs := halfUp_split k
  have hb := Tuza.halfUp_balanced k
  have hq : 2 ≤ n / (2 * Tuza.halfUp k) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  unfold runCount
  omega

theorem runRemainder_lt (n k : ℕ) (hk : 0 < k) :
    runRemainder n k < 2 * Tuza.halfUp k := by
  have hp := Tuza.halfUp_pos hk
  have hm := Nat.mod_add_div n (2 * Tuza.halfUp k)
  have hl := Nat.mod_lt n (by omega : 0 < 2 * Tuza.halfUp k)
  unfold runRemainder runCount
  have he : 2 * (n / (2 * Tuza.halfUp k)) * Tuza.halfUp k =
      2 * Tuza.halfUp k * (n / (2 * Tuza.halfUp k)) := by ring
  rw [he]
  omega

theorem runCapacity (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 2 ≤ n) :
    runRemainder n k ≤ k / 2 * runCount n k := by
  have hr := runCount_four n k hk hn
  have hR := runRemainder_lt n k (by omega)
  have hs := halfUp_split k
  have hb := Tuza.halfUp_balanced k
  have hp : 1 ≤ k / 2 := by omega
  have hhalf : Tuza.halfUp k ≤ k / 2 + 1 := by omega
  have hm := Nat.mul_le_mul_left (k / 2) hr
  nlinarith

theorem runLength_bounds (n k : ℕ) (i : Fin (runCount n k)) :
    Tuza.halfUp k ≤ runLength n k i ∧ runLength n k i ≤ k := by
  have hs := halfUp_split k
  have hm := Nat.min_le_left (k / 2) (runRemainder n k - k / 2 * i.val)
  unfold runLength
  omega

theorem runLength_positive (n k : ℕ) (hk : 0 < k) (i : Fin (runCount n k)) :
    0 < runLength n k i :=
  (Tuza.halfUp_pos hk).trans_le (runLength_bounds n k i).1

theorem runLength_sum (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 2 ≤ n) :
    ∑ i : Fin (runCount n k), runLength n k i = n := by
  have hc := runCapacity n k hk hn
  have hb := Nat.div_mul_le_self n (2 * Tuza.halfUp k)
  have he : n / (2 * Tuza.halfUp k) * (2 * Tuza.halfUp k) =
      runCount n k * Tuza.halfUp k := by unfold runCount; ring
  rw [he] at hb
  simp only [runLength, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, fill_sum, Nat.min_eq_left hc]
  unfold runRemainder
  norm_cast
  omega

end ResearchMain.PathCycleTuza
