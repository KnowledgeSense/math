import TerminalLogConcavity.BlockEntropy

namespace TerminalLogConcavity

theorem power_error_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (hsmall : (n : ℝ) * x ≤ 1 / 2) : (1 + x) ^ n - 1 ≤ 2 * (n : ℝ) * x := by
  have hb : 1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + x) hb n
  rw [← Real.exp_nat_mul] at hp
  have hn : 0 ≤ (n : ℝ) * x := by positivity
  have he := Real.exp_bound_div_one_sub_of_interval hn (by linarith)
  have hd : 0 < 1 - (n : ℝ) * x := by linarith
  have hdiv : 1 / (1 - (n : ℝ) * x) ≤ 1 + 2 * (n : ℝ) * x := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  linarith

theorem transfer_row_error_real {q u z : ℝ} (n : ℕ)
    (hq : 0 ≤ q) (hu : 0 ≤ u) (hz : 1 ≤ z)
    (hsmall : 8 * (n : ℝ) ≤ z)
    (hweight : 32 * q * (n : ℝ) * (u + 2) ≤ z) :
    4 * q * (u + 2) * ((z ^ 2 + 3 * z + 1) ^ n - (z ^ 2) ^ n) ≤ (z ^ 2) ^ n := by
  have hz0 : 0 < z := by linarith
  have hz2 : 0 < z ^ 2 := by positivity
  let x := (3 * z + 1) / z ^ 2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxupper : x ≤ 4 / z := by
    dsimp [x]
    apply (div_le_div_iff₀ hz2 hz0).mpr
    nlinarith
  have hnx : (n : ℝ) * x ≤ 4 * (n : ℝ) / z := by
    have h := mul_le_mul_of_nonneg_left hxupper (show 0 ≤ (n : ℝ) by positivity)
    convert h using 1 ; ring
  have hhalf : (n : ℝ) * x ≤ 1 / 2 :=
    hnx.trans ((div_le_iff₀ hz0).mpr (by linarith))
  have hp := power_error_le hx n hhalf
  have hfactor : z ^ 2 + 3 * z + 1 = z ^ 2 * (1 + x) := by
    dsimp [x]
    field_simp
    ring
  have hdiff : (z ^ 2 + 3 * z + 1) ^ n - (z ^ 2) ^ n =
      (z ^ 2) ^ n * ((1 + x) ^ n - 1) := by rw [hfactor, mul_pow]; ring
  have hcontrol : 4 * q * (u + 2) * (2 * (n : ℝ) * x) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hnx (by positivity : 0 ≤ 8 * q * (u + 2))
    have hd : 32 * q * (n : ℝ) * (u + 2) / z ≤ 1 :=
      (div_le_iff₀ hz0).mpr (by simpa using hweight)
    have heq : 8 * q * (u + 2) * (4 * (n : ℝ) / z) =
        32 * q * (n : ℝ) * (u + 2) / z := by ring
    rw [heq] at hm
    nlinarith
  rw [hdiff]
  have h1 := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4 * q * (u + 2) * (z ^ 2) ^ n)
  have h2 := mul_le_mul_of_nonneg_left hcontrol (by positivity : 0 ≤ (z ^ 2) ^ n)
  nlinarith

theorem transfer_row_error_nat {q a i : ℕ} (hq : 2 ≤ q) (ha : 128 * q ^ 4 ≤ a)
    (hi : i ≤ q) :
    let z := a ^ (2 * q ^ 2)
    let u := a ^ (i ^ 2)
    4 * q * (u + 2) * ((z ^ 2 + 3 * z + 1) ^ (q - 1) - (z ^ 2) ^ (q - 1)) ≤
      (z ^ 2) ^ (q - 1) := by
  dsimp
  let r := a ^ (q ^ 2)
  let z := a ^ (2 * q ^ 2)
  let u := a ^ (i ^ 2)
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith
  have ha1 : 1 ≤ a := by nlinarith
  have hr : a ≤ r := by
    have h := Nat.pow_le_pow_right (by omega : 0 < a) hq2
    simpa [r] using h
  have hr1 : 1 ≤ r := by omega
  have hur : u ≤ r := Nat.pow_le_pow_right (by omega : 0 < a) (Nat.pow_le_pow_left hi 2)
  have hzeq : z = r ^ 2 := by dsimp [z, r]; rw [← pow_mul]; congr 1; ring
  have hz1 : 1 ≤ z := by rw [hzeq]; exact Nat.one_le_pow 2 r (by omega)
  have hmargin : 96 * q ^ 2 ≤ r := by nlinarith
  have hqu : 32 * q * (q - 1) * (u + 2) ≤ z := by
    have hnm : q - 1 ≤ q := by omega
    have hbase : u + 2 ≤ 3 * r := by omega
    have h1 := Nat.mul_le_mul_right (32 * q * (u + 2)) hnm
    have h2 := Nat.mul_le_mul_left (32 * q ^ 2) hbase
    have h3 := Nat.mul_le_mul_right r hmargin
    rw [hzeq]
    nlinarith
  have hsmall : 8 * (q - 1) ≤ z := by
    have hn : q - 1 ≤ q := by omega
    have hqq : q ≤ q ^ 2 := by nlinarith
    have hrr : r ≤ r ^ 2 := by nlinarith
    rw [hzeq]
    nlinarith
  have hreal := transfer_row_error_real (q := (q : ℝ)) (u := (u : ℝ)) (z := (z : ℝ)) (q - 1)
    (by positivity) (by positivity) (by exact_mod_cast hz1)
    (by exact_mod_cast hsmall) (by exact_mod_cast hqu)
  have hdiff : (z ^ 2) ^ (q - 1) ≤ (z ^ 2 + 3 * z + 1) ^ (q - 1) :=
    Nat.pow_le_pow_left (by omega) _
  have hcast : ((4 * q * (u + 2) *
      ((z ^ 2 + 3 * z + 1) ^ (q - 1) - (z ^ 2) ^ (q - 1)) : ℕ) : ℝ) ≤
      (((z ^ 2) ^ (q - 1) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hdiff]
    exact hreal
  exact_mod_cast hcast

end TerminalLogConcavity
