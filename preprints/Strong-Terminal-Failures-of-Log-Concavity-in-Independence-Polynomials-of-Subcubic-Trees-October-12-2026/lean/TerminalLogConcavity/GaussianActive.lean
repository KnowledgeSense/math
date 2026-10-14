import TerminalLogConcavity.GaussianTails
import TerminalLogConcavity.BinomialPolynomial
import TerminalLogConcavity.RealCoefficientOrder
import Mathlib.Tactic.FieldSimp

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

theorem gaussian_distance_identity (i u : ℕ) :
    2 * i * u + (Nat.dist i u) ^ 2 = i ^ 2 + u ^ 2 := by
  by_cases hi : i ≤ u
  · rw [Nat.dist_eq_sub_of_le hi]
    have h := Nat.sub_add_cancel hi
    nlinarith
  · rw [Nat.dist_eq_sub_of_le_right (by omega)]
    have h := Nat.sub_add_cancel (show u ≤ i by omega)
    nlinarith

theorem gaussian_power_identity {a : ℝ} (ha : 0 < a) (i u : ℕ) :
    (1 / a) ^ (i ^ 2) * a ^ (2 * i * u) =
      a ^ (u ^ 2) * (1 / a) ^ ((Nat.dist i u) ^ 2) := by
  have he : a ^ (2 * i * u) * a ^ ((Nat.dist i u) ^ 2) = a ^ (i ^ 2) * a ^ (u ^ 2) := by
    rw [← pow_add, ← pow_add, gaussian_distance_identity]
  simp only [one_div] at *
  apply (mul_left_cancel₀ (pow_ne_zero (i ^ 2) (ne_of_gt ha)))
  apply (mul_right_cancel₀ (pow_ne_zero ((Nat.dist i u) ^ 2) (ne_of_gt ha)))
  calc
    _ = a ^ (2 * i * u) * a ^ ((Nat.dist i u) ^ 2) := by
      field_simp [ne_of_gt ha]
      rw [← mul_pow]
      simp [ne_of_gt ha]
    _ = _ := he
    _ = _ := by
      field_simp [ne_of_gt ha]
      rw [← mul_pow]
      simp [ne_of_gt ha]

noncomputable def normalizedActive (q : ℕ) (a lam : ℝ) (i : ℕ) : ℝ[X] :=
  C ((1 / a) ^ ((i + 1) ^ 2)) * ((1 + C (lam * a ^ (2 * (i + 1))) * X) ^ q).erase 0

noncomputable def gaussianActiveSum (q : ℕ) (a lam : ℝ) : ℝ[X] :=
  ∑ i ∈ Finset.range q, normalizedActive q a lam i

@[simp] theorem normalizedActive_zero (q : ℕ) (a lam : ℝ) (i : ℕ) :
    (normalizedActive q a lam i).coeff 0 = 0 := by simp [normalizedActive]

theorem normalizedActive_coefficient {q i u : ℕ} {a lam : ℝ} (ha : 0 < a) (hu : 1 ≤ u) :
    (normalizedActive q a lam i).coeff u =
      (q.choose u : ℝ) * lam ^ u * a ^ (u ^ 2) * (1 / a) ^ ((Nat.dist (i + 1) u) ^ 2) := by
  have hu0 : u ≠ 0 := by omega
  simp only [normalizedActive, coeff_C_mul, coeff_erase, hu0, ite_false]
  rw [weighted_binomial_coeff_semiring, mul_pow, ← pow_mul]
  calc
    _ = (q.choose u : ℝ) * lam ^ u * ((1 / a) ^ ((i + 1) ^ 2) * a ^ (2 * (i + 1) * u)) := by ring
    _ = _ := by rw [gaussian_power_identity ha]; ring

theorem normalizedActive_nonnegative {q i : ℕ} {a lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) :
    CoeffNonnegative (normalizedActive q a lam i) := by
  intro u
  by_cases hu : u = 0
  · subst u; simp
  · rw [normalizedActive_coefficient ha (by omega)]
    positivity

@[simp] theorem gaussianActiveSum_zero (q : ℕ) (a lam : ℝ) :
    (gaussianActiveSum q a lam).coeff 0 = 0 := by simp [gaussianActiveSum]

theorem gaussianActiveSum_nonnegative {q : ℕ} {a lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) :
    CoeffNonnegative (gaussianActiveSum q a lam) := by
  intro u
  simp only [gaussianActiveSum, finsetSum_coeff]
  exact Finset.sum_nonneg (fun i _ => normalizedActive_nonnegative ha hlam u)

theorem gaussianActiveSum_coefficient {q u : ℕ} {a lam : ℝ} (ha : 2 ≤ a)
    (hlam : 0 ≤ lam) (hu : 1 ≤ u) :
    (gaussianActiveSum q a lam).coeff u ≤
      (1 + 4 / a) * (q.choose u : ℝ) * lam ^ u * a ^ (u ^ 2) := by
  have ha0 : 0 < a := by linarith
  have hinv : 1 / a ≤ 1 / 2 := (div_le_div_iff₀ ha0 (by norm_num)).mpr (by linarith)
  have ht := finite_shifted_gaussian_bound (by positivity : 0 ≤ 1 / a) hinv
    ((Finset.range q).image Nat.succ) u
  rw [Finset.sum_image (by intro i _ j _ h; exact Nat.succ.inj h)] at ht
  have he : (gaussianActiveSum q a lam).coeff u =
      ((q.choose u : ℝ) * lam ^ u * a ^ (u ^ 2)) *
        (∑ i ∈ Finset.range q, (1 / a) ^ ((Nat.dist (i + 1) u) ^ 2)) := by
    simp only [gaussianActiveSum, finsetSum_coeff, normalizedActive_coefficient ha0 hu,
      Finset.mul_sum]
  rw [he]
  have h := mul_le_mul_of_nonneg_left ht
    (by positivity : 0 ≤ (q.choose u : ℝ) * lam ^ u * a ^ (u ^ 2))
  convert h using 1 ; ring

end TerminalLogConcavity
