import MainTheorems.Domination.Basic

namespace ResearchMain.Domination

theorem binomial_normalized_lc (n k : ℕ) (hk : k + 2 ≤ n) (a b c : ℚ)
    (h : ((n - k : ℕ) : ℚ) * (k + 2) * a * c ≤
      ((n - k - 1 : ℕ) : ℚ) * (k + 1) * b ^ 2) :
    (a / Nat.choose n k) * (c / Nat.choose n (k + 2)) ≤
      (b / Nat.choose n (k + 1)) ^ 2 := by
  let bp : ℚ := Nat.choose n k
  let bm : ℚ := Nat.choose n (k + 1)
  let bn : ℚ := Nat.choose n (k + 2)
  have hbp : 0 < bp := by
    dsimp [bp]
    exact_mod_cast Nat.choose_pos (by omega : k ≤ n)
  have hbm : 0 < bm := by
    dsimp [bm]
    exact_mod_cast Nat.choose_pos (by omega : k + 1 ≤ n)
  have hbn : 0 < bn := by
    dsimp [bn]
    exact_mod_cast Nat.choose_pos hk
  have hprev : bm * (k + 1) = bp * ((n - k : ℕ) : ℚ) := by
    dsimp [bm, bp]
    exact_mod_cast Nat.choose_succ_right_eq n k
  have hnext : bn * (k + 2) = bm * ((n - k - 1 : ℕ) : ℚ) := by
    dsimp [bn, bm]
    have hn : n - (k + 1) = n - k - 1 := by omega
    have hi : k + 1 + 1 = k + 2 := by omega
    exact_mod_cast (hi ▸ hn ▸ Nat.choose_succ_right_eq n (k + 1))
  have hcoef : (bp * bn) * (((n - k : ℕ) : ℚ) * (k + 2)) =
      bm ^ 2 * (((n - k - 1 : ℕ) : ℚ) * (k + 1)) := by
    calc
      _ = (bp * ((n - k : ℕ) : ℚ)) * (bn * (k + 2)) := by ring
      _ = (bm * (k + 1)) * (bm * ((n - k - 1 : ℕ) : ℚ)) := by rw [← hprev, hnext]
      _ = _ := by ring
  have hpos : (0 : ℚ) < ((n - k : ℕ) : ℚ) * (k + 2) := by
    have hn : 0 < n - k := by omega
    positivity
  have hscaled : (((n - k : ℕ) : ℚ) * (k + 2)) * (a * c * bm ^ 2) ≤
      (((n - k : ℕ) : ℚ) * (k + 2)) * (b ^ 2 * bp * bn) := by
    have hm := mul_le_mul_of_nonneg_left h (sq_nonneg bm)
    calc
      _ = bm ^ 2 * (((n - k : ℕ) : ℚ) * (k + 2) * a * c) := by ring
      _ ≤ bm ^ 2 * (((n - k - 1 : ℕ) : ℚ) * (k + 1) * b ^ 2) := hm
      _ = (bm ^ 2 * (((n - k - 1 : ℕ) : ℚ) * (k + 1))) * b ^ 2 := by ring
      _ = _ := by rw [← hcoef]; ring
  have hfinal := le_of_mul_le_mul_left hscaled hpos
  change (a / bp) * (c / bn) ≤ (b / bm) ^ 2
  rw [div_mul_div_comm, div_pow]
  apply (div_le_div_iff₀ (mul_pos hbp hbn) (sq_pos_of_pos hbm)).mpr
  simpa only [mul_assoc] using hfinal

end ResearchMain.Domination
