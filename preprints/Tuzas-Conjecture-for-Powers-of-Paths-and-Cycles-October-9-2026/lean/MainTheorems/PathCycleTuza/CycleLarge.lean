import MainTheorems.PathCycleTuza.CyclicPacking
import MainTheorems.PathCycleTuza.RunCover
import MainTheorems.PathCycleTuza.PathArithmetic

namespace ResearchMain.PathCycleTuza

open Tuza

theorem residueOrder_density (r t : ℕ) (hr : 7 ≤ r) (hrb : r ≤ 18) :
    (r + 12 * t) / 2 ≤ 2 * residueOrder r t := by
  unfold residueOrder
  interval_cases r <;> norm_num [baseOrder] <;> omega

theorem cycle_exponent_arithmetic (k : ℕ) (hk : 7 ≤ k) :
    ∃ m : ℕ, 3 * m + hookFlag m ≤ k ∧ k / 2 ≤ 2 * m := by
  let r := (k - 7) % 12 + 7
  let t := (k - 7) / 12
  have hr : 7 ≤ r := by dsimp [r]; omega
  have hrb : r ≤ 18 := by dsimp [r]; omega
  have he : k = r + 12 * t := by dsimp [r, t]; omega
  refine ⟨residueOrder r t, ?_, ?_⟩
  · have h := residueOrder_bounded r t hr hrb
    omega
  · rw [he]
    exact residueOrder_density r t hr hrb

theorem cycle_skolem_inequality (n k m : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 2 ≤ n)
    (hm : 3 * m + hookFlag m ≤ k) (hd : k / 2 ≤ 2 * m) : Inequality (cyclePower n k) := by
  have hc := cycle_run_cover n k hk hn
  have hp := skolem_cycle_bound n k m hm (by omega)
  have hm' := Nat.mul_le_mul_right n hd
  unfold Inequality
  nlinarith

theorem cycle_large_inequality (n k : ℕ) (hk : 7 ≤ k) (hn : 2 * k + 2 ≤ n) :
    Inequality (cyclePower n k) := by
  obtain ⟨m, hm, hd⟩ := cycle_exponent_arithmetic k hk
  exact cycle_skolem_inequality n k m (by omega) hn hm hd

theorem cycle_three_to_five (n k : ℕ) (hk : 3 ≤ k) (hu : k ≤ 5) : Inequality (cyclePower n k) := by
  by_cases hn : n ≤ 2 * k + 1
  · rw [cyclePower_complete n k hn]
    exact complete_inequality n
  · apply cycle_skolem_inequality n k 1 (by omega) (by omega)
    · norm_num [hookFlag]
      omega
    · omega

theorem cycle_zero_inequality (n : ℕ) : Inequality (cyclePower n 0) := by
  rw [cyclePower_zero]
  exact bottom_inequality _

theorem cycle_one_inequality (n : ℕ) : Inequality (cyclePower n 1) := by
  by_cases hn : n ≤ 3
  · rw [cyclePower_complete n 1 (by omega)]
    exact complete_inequality n
  · exact triangleFree_inequality _ (cyclePower_one_triangleFree n (by omega))

end ResearchMain.PathCycleTuza
