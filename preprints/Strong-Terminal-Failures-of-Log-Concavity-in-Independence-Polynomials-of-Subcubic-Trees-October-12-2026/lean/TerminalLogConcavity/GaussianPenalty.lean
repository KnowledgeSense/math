import TerminalLogConcavity.GaussianConvolution
import TerminalLogConcavity.BinomialBounds

namespace TerminalLogConcavity
open scoped Polynomial

theorem three_mul_le_eight_power {k : ℕ} (hk : 2 ≤ k) : 3 * k ≤ 8 ^ (k - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero => decide
  | succ m ih =>
    have he : 2 + (m + 1) - 1 = (2 + m - 1) + 1 := by omega
    rw [he, pow_succ]
    omega

theorem gaussian_penalty_base {a : ℝ} (ha : 256 ≤ a) {k : ℕ} (hk : 2 ≤ k) :
    (3 * (k : ℝ)) / a ^ (k - 1) ≤ (1 / 32 : ℝ) ^ (k - 1) := by
  have ha0 : 0 < a := by linarith
  have hkbound : 3 * (k : ℝ) ≤ (8 : ℝ) ^ (k - 1) := by exact_mod_cast three_mul_le_eight_power hk
  have hdiv : (8 : ℝ) / a ≤ 1 / 32 := (div_le_iff₀ ha0).mpr (by linarith)
  calc
    _ ≤ (8 : ℝ) ^ (k - 1) / a ^ (k - 1) := div_le_div_of_nonneg_right hkbound (by positivity)
    _ = (8 / a) ^ (k - 1) := (div_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hdiv _

theorem gaussian_penalty_power {a : ℝ} (ha : 256 ≤ a) {k j : ℕ} (hk : 2 ≤ k) (hj : 1 ≤ j) :
    ((3 * (k : ℝ)) / a ^ (k - 1)) ^ j ≤ (1 / 32 : ℝ) ^ (k - 1) := by
  have ha0 : 0 < a := by linarith
  have hb := gaussian_penalty_base ha hk
  have hunit : (1 / 32 : ℝ) ^ (k - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hnonneg : 0 ≤ (3 * (k : ℝ)) / a ^ (k - 1) := by positivity
  calc
    _ ≤ ((1 / 32 : ℝ) ^ (k - 1)) ^ j := pow_le_pow_left₀ hnonneg hb j
    _ ≤ ((1 / 32 : ℝ) ^ (k - 1)) ^ 1 := pow_le_pow_of_le_one (by positivity) hunit hj
    _ = _ := pow_one _

theorem power_penalty_identity {a b : ℝ} (ha : 0 < a) {k j : ℕ} (hkj : k ≤ j) :
    a ^ (j ^ 2 - (k - 1) * j) * b ^ j =
      a ^ (j ^ 2) * (b / a ^ (k - 1)) ^ j := by
  have hk : (k - 1) * j ≤ j ^ 2 := by
    have h := Nat.mul_le_mul_right j (show k - 1 ≤ j by omega)
    nlinarith
  have he := Nat.sub_add_cancel hk
  have hp : a ^ (j ^ 2 - (k - 1) * j) * a ^ ((k - 1) * j) = a ^ (j ^ 2) := by
    rw [← pow_add, he]
  rw [div_pow, ← pow_mul]
  apply (mul_right_cancel₀ (pow_ne_zero ((k - 1) * j) (ne_of_gt ha)))
  calc
    _ = (a ^ (j ^ 2 - (k - 1) * j) * a ^ ((k - 1) * j)) * b ^ j := by ring
    _ = a ^ (j ^ 2) * b ^ j := by rw [hp]
    _ = _ := by field_simp

theorem gaussian_tail_factor {k : ℕ} (hk : 2 ≤ k) :
    (2 : ℝ) ^ k * (1 / 32 : ℝ) ^ (k - 1) ≤ (1 / 4 : ℝ) ^ (k - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have he : 2 + n - 1 = n + 1 := by omega
  rw [he]
  have hpow : (1 / 16 : ℝ) ^ n ≤ (1 / 4 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hid : (2 : ℝ) ^ n * (1 / 32 : ℝ) ^ n = (1 / 16 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  calc
    _ = (1 / 8 : ℝ) * (1 / 16 : ℝ) ^ n := by rw [← hid]; ring
    _ ≤ (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ n := by
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n]
    _ = _ := by rw [pow_succ]; ring

theorem gaussian_power_tail_bound {S : ℝ[X]} {q k j : ℕ} {a lam θ : ℝ}
    (hS : CoeffNonnegative S) (hzero : S.coeff 0 = 0)
    (ha : 256 ≤ a) (hlam : 0 ≤ lam) (hθ : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hcoeff : ∀ u, 1 ≤ u → S.coeff u ≤ θ * (q.choose u : ℝ) * lam ^ u * a ^ (u ^ 2))
    (hj : 1 ≤ j) (hjq : j ≤ q) (hk : 2 ≤ k) :
    (S ^ k).coeff j ≤ (1 / 4 : ℝ) ^ (k - 1) * ((q.choose j : ℝ) * lam ^ j * a ^ (j ^ 2)) := by
  have ha0 : 0 < a := by linarith
  by_cases hkj : k ≤ j
  · have hc := gaussian_power_coefficient_bound hS hzero (by linarith : 1 ≤ a) hlam hθ hcoeff k j
    have hb : ((k * q).choose j : ℝ) ≤ (3 * (k : ℝ)) ^ j * (q.choose j : ℝ) := by
      exact_mod_cast choose_dilated_bound hjq k
    have hm := mul_le_mul_of_nonneg_left hb
      (by positivity : 0 ≤ θ ^ k * lam ^ j * a ^ (j ^ 2 - (k - 1) * j))
    have he : θ ^ k * lam ^ j * a ^ (j ^ 2 - (k - 1) * j) *
        ((3 * (k : ℝ)) ^ j * (q.choose j : ℝ)) =
        (θ ^ k * ((3 * (k : ℝ)) / a ^ (k - 1)) ^ j) *
          ((q.choose j : ℝ) * lam ^ j * a ^ (j ^ 2)) := by
      calc
        _ = θ ^ k * (lam ^ j * (q.choose j : ℝ)) *
            (a ^ (j ^ 2 - (k - 1) * j) * (3 * (k : ℝ)) ^ j) := by ring
        _ = _ := by rw [power_penalty_identity ha0 hkj]; ring
    rw [he] at hm
    have ht := pow_le_pow_left₀ hθ hθ2 k
    have hp := gaussian_penalty_power ha hk hj
    have htp := mul_le_mul ht hp (by positivity) (by positivity)
    have hfin := mul_le_mul_of_nonneg_right (htp.trans (gaussian_tail_factor hk))
      (by positivity : 0 ≤ (q.choose j : ℝ) * lam ^ j * a ^ (j ^ 2))
    exact hc.trans (hm.trans hfin)
  · rw [polynomial_power_coeff_zero_of_lt S hzero (by omega)]
    positivity

end TerminalLogConcavity
