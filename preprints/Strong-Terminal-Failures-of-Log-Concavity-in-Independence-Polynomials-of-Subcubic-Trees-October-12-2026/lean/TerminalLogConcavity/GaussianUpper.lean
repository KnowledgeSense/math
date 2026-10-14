import TerminalLogConcavity.GaussianNormalization
import TerminalLogConcavity.GaussianPenalty

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

theorem geometric_power_coefficient_bound {S : ℝ[X]} {q j : ℕ} {a lam θ : ℝ}
    (hq : 2 ≤ q) (hjq : j ≤ q) (hS : CoeffNonnegative S) (hzero : S.coeff 0 = 0)
    (ha : 256 ≤ a) (hlam : 0 ≤ lam) (hθ : 0 ≤ θ) (hθmax : θ ≤ 3 / 2)
    (hcoeff : ∀ u, 1 ≤ u → S.coeff u ≤ θ * (q.choose u : ℝ) * lam ^ u * a ^ (u ^ 2)) :
    (∑ k ∈ Finset.range (q + 1), S ^ k).coeff j ≤
      2 * ((q.choose j : ℝ) * lam ^ j * a ^ (j ^ 2)) := by
  rw [finsetSum_coeff]
  by_cases hj0 : j = 0
  · subst j
    have hz (k : ℕ) : (S ^ k).coeff 0 = if k = 0 then 1 else 0 := by
      cases k with
      | zero => simp
      | succ k => rw [pow_succ, mul_coeff_zero, hzero, mul_zero]; simp
    simp only [hz]
    simp
  · have hj : 1 ≤ j := by omega
    have ha0 : 0 < a := by linarith
    let γ : ℝ := (q.choose j : ℝ) * lam ^ j * a ^ (j ^ 2)
    have hγ : 0 ≤ γ := by dsimp [γ]; positivity
    have hhead : S.coeff j ≤ (3 / 2) * γ := by
      have h := hcoeff j hj
      have hm := mul_le_mul_of_nonneg_right hθmax hγ
      dsimp [γ] at *
      nlinarith
    have htail : (∑ n ∈ Finset.range (q - 1), (S ^ (2 + n)).coeff j) ≤ (1 / 3) * γ := by
      calc
        _ ≤ ∑ n ∈ Finset.range (q - 1), (1 / 4 : ℝ) ^ (n + 1) * γ := by
          apply Finset.sum_le_sum
          intro n _
          have h := gaussian_power_tail_bound hS hzero ha hlam hθ (by linarith) hcoeff hj hjq
            (show 2 ≤ 2 + n by omega)
          simpa only [show 2 + n - 1 = n + 1 by omega] using h
        _ = (∑ n ∈ Finset.range (q - 1), (1 / 4 : ℝ) ^ (n + 1)) * γ := by rw [Finset.sum_mul]
        _ ≤ (1 / 3) * γ := by
          have h := geometric_initial_bound (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) (q - 1)
          norm_num at h
          exact mul_le_mul_of_nonneg_right h hγ
    have he : q + 1 = 2 + (q - 1) := by omega
    rw [he, Finset.sum_range_add]
    have hfirst : (∑ k ∈ Finset.range 2, (S ^ k).coeff j) = S.coeff j := by
      simp [Finset.sum_range_succ, coeff_one, hj0]
    rw [hfirst]
    change _ ≤ 2 * γ
    linarith

theorem gaussian_coefficient_upper {q a lam j : ℕ} (hq : 2 ≤ q) (ha : 256 ≤ a) (hj : j ≤ q) :
    ((gaussianPolynomial q a lam).coeff j : ℝ) ≤
      3 * (q.choose j : ℝ) * (lam : ℝ) ^ j * (a : ℝ) ^ (squareSum q + j ^ 2) := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have har : (256 : ℝ) ≤ a := by exact_mod_cast ha
  have hθ : 0 ≤ 1 + 4 / (a : ℝ) := by positivity
  have hθmax : 1 + 4 / (a : ℝ) ≤ 3 / 2 := by
    have h : 4 / (a : ℝ) ≤ 1 / 2 := (div_le_iff₀ ha0).mpr (by linarith)
    linarith
  have hg := geometric_power_coefficient_bound hq hj
    (gaussianActiveSum_nonnegative ha0 (show 0 ≤ (lam : ℝ) by positivity))
    (gaussianActiveSum_zero q a lam) har (show 0 ≤ (lam : ℝ) by positivity) hθ hθmax
    (fun u hu => gaussianActiveSum_coefficient (by linarith : (2 : ℝ) ≤ a) (by positivity) hu)
  have hm := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ (3 / 2 : ℝ) * (a : ℝ) ^ squareSum q)
  have hpoly := gaussian_polynomial_majorization (q := q) (lam := lam) ha j
  rw [realPolynomial_coeff, coeff_C_mul] at hpoly
  apply hpoly.trans
  convert hm using 1 ; rw [pow_add] ; ring

end TerminalLogConcavity
