import MainTheorems.PathCycleTuza.SkolemExistence

namespace ResearchMain.PathCycleTuza

def baseOrder (r : ℕ) : ℕ := if r ≤ 9 then 2 else if r ≤ 11 then 3 else if r ≤ 14 then 4 else 5

def residueOrder (r t : ℕ) : ℕ := 4 * t + baseOrder r

theorem hookFlag_four_add (t b : ℕ) : hookFlag (4 * t + b) = hookFlag b := by
  simp [hookFlag, Nat.add_mod]

theorem residueOrder_bounded (r t : ℕ) (hr : 7 ≤ r) (hrb : r ≤ 18) :
    3 * residueOrder r t + hookFlag (residueOrder r t) ≤ r + 12 * t := by
  unfold residueOrder
  rw [hookFlag_four_add]
  interval_cases r <;> norm_num [baseOrder, hookFlag] <;> omega

theorem residue_path_arithmetic (r t k n : ℕ) (hr : 7 ≤ r) (hrb : r ≤ 18)
    (hk : k = r + 12 * t) (hn : 2 * k + 2 ≤ n) (he₈ : k ≠ 8) (he₉ : k ≠ 9) :
    2 * ((k / 2 : ℕ) : ℤ) * ((n : ℤ) - (k / 2 : ℕ) - 1) ≤
      4 * (residueOrder r t : ℤ) * n - 9 * (residueOrder r t : ℤ) ^ 2 -
        3 * residueOrder r t - 2 * hookFlag (residueOrder r t) := by
  have ht : (0 : ℤ) ≤ t := by positivity
  have hhalf : k / 2 = 6 * t + r / 2 := by omega
  have hkr : (k : ℤ) = r + 12 * t := by exact_mod_cast hk
  have hnr : (0 : ℤ) ≤ (n : ℤ) - (24 * t + 2 * r + 2) := by
    have h : 2 * (k : ℤ) + 2 ≤ n := by exact_mod_cast hn
    linarith
  have hcoef : (0 : ℤ) ≤ 4 * t + 4 * baseOrder r - 2 * (r / 2 : ℕ) := by
    interval_cases r <;> norm_num [baseOrder] <;> linarith
  have hprod := mul_nonneg hcoef hnr
  have he : r = 8 ∨ r = 9 → 1 ≤ t := by omega
  unfold residueOrder
  rw [hookFlag_four_add, hhalf]
  push_cast
  interval_cases r <;> norm_num [baseOrder, hookFlag] at * <;> nlinarith [sq_nonneg (t : ℤ)]

theorem path_exponent_arithmetic (k n : ℕ) (hk : 7 ≤ k) (hn : 2 * k + 2 ≤ n)
    (he₈ : k ≠ 8) (he₉ : k ≠ 9) : ∃ m : ℕ, 3 * m + hookFlag m ≤ k ∧
      2 * ((k / 2 : ℕ) : ℤ) * ((n : ℤ) - (k / 2 : ℕ) - 1) ≤
        4 * (m : ℤ) * n - 9 * (m : ℤ) ^ 2 - 3 * m - 2 * hookFlag m := by
  let r := (k - 7) % 12 + 7
  let t := (k - 7) / 12
  have hr : 7 ≤ r := by dsimp only [r]; omega
  have hrb : r ≤ 18 := by dsimp only [r]; omega
  have hkr : k = r + 12 * t := by dsimp only [r, t]; omega
  refine ⟨residueOrder r t, ?_, residue_path_arithmetic r t k n hr hrb hkr hn he₈ he₉⟩
  have h := residueOrder_bounded r t hr hrb
  omega

end ResearchMain.PathCycleTuza
