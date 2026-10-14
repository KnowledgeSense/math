import HilbertBipartite.SignPositivity
import Mathlib.Tactic.LinearCombination

open Finset Polynomial

namespace HilbertBipartite

private theorem partial_sum_pascal (m i : ℕ) :
    (∑ j ∈ range (m+1), C ((-1 : ℚ)^j * ((i+1).choose j : ℚ)) * (1-X)^j) =
      X * (∑ j ∈ range (m+1), C ((-1 : ℚ)^j * (i.choose j : ℚ)) * (1-X)^j) +
        C ((-1 : ℚ)^m * (i.choose m : ℚ)) * (1-X)^(m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [sum_range_succ _ (m+1), ih, Nat.choose_succ_succ]
    push_cast
    simp only [pow_succ, map_add, map_mul, map_neg, map_one]
    ring

private theorem gPoly_pascal (m i : ℕ) (hm : m ≤ i) :
    gPoly (m+1) (i+2) = X * gPoly (m+1) (i+1) +
      C ((-1 : ℚ)^m * (i.choose m : ℚ)) * (1-X)^(m+1) := by
  rw [gPoly_partial (m+1) (i+2) (by omega) (by omega),
    gPoly_partial (m+1) (i+1) (by omega) (by omega)]
  simpa using partial_sum_pascal m i

private theorem gPoly_succ (m i : ℕ) (hm : m+1 ≤ i) (hi : 1 ≤ i) :
    gPoly (m+1) i = gPoly m i + C ((-1 : ℚ)^m * ((i-1).choose m : ℚ)) * (1-X)^m := by
  rw [gPoly_partial (m+1) i hi hm, gPoly_partial m i hi (by omega), sum_range_succ]

private theorem gPoly_adjacent (m i : ℕ) (hm : m < i) :
    C ((i-m : ℕ) : ℚ) * gPoly (m+1) (i+2) +
      C ((m+1 : ℕ) : ℚ) * gPoly (m+2) (i+2) =
      C ((i+1 : ℕ) : ℚ) * (X * gPoly (m+1) (i+1)) := by
  have hn : ((m+1 : ℕ) : ℚ) * ((i+1).choose (m+1) : ℚ) =
      ((i+1 : ℕ) : ℚ) * (i.choose m : ℚ) := by
    exact_mod_cast (Nat.mul_comm _ _).trans (Nat.add_one_mul_choose_eq i m).symm
  have hnC := congrArg (fun q : ℚ => C q) hn
  simp only [map_mul] at hnC
  rw [gPoly_succ (m+1) (i+2) (by omega) (by omega),
    gPoly_pascal m i (by omega)]
  simp only [show i+2-1=i+1 by omega, pow_succ, map_mul, map_neg, map_one,
    Nat.cast_sub (by omega : m ≤ i), Nat.cast_add, Nat.cast_one, map_sub, map_add] at *
  linear_combination -C ((-1 : ℚ)^m) * (1-X)^m * (1-X) * hnC

private theorem signed_weighted_gPoly_nonneg (m j i r : ℕ)
    (hm : 1 ≤ m) (hj : m < j) (hji : j ≤ i) :
    0 ≤ (-1 : ℚ)^(m-1) * weightedCoeff (gPoly m j) i r := by
  rw [← weightedCoeff_C_mul, signed_gPoly_expansion m j (by omega) (by omega),
    weightedCoeff_sum]
  apply sum_nonneg
  intro c hc
  rw [weightedCoeff_C_mul, weightedCoeff_cancel_pow c i r (by have := mem_range.mp hc; omega)]
  exact mul_nonneg (signedTransform_coeff_nonneg m j hm hj c) (by positivity)

private theorem normalized_tau_succ_le_aux (m i r : ℕ) (hm : m < i) :
    ((-1 : ℚ)^(m+1) * tau (m+2) (i+2) r) / (i.choose (m+1) : ℚ) ≤
      ((-1 : ℚ)^m * tau (m+1) (i+2) r) / (i.choose m : ℚ) := by
  have hw := congrArg (fun P : Polynomial ℚ => weightedCoeff P (i+2) r)
    (gPoly_adjacent m i hm)
  simp only [weightedCoeff_add, weightedCoeff_C_mul] at hw
  have hn : 0 ≤ (-1 : ℚ)^m * weightedCoeff (X*gPoly (m+1) (i+1)) (i+2) r := by
    cases r with
    | zero => simp
    | succ r =>
      rw [weightedCoeff_X_mul_succ]
      simpa using signed_weighted_gPoly_nonneg (m+1) (i+1) (i+2) r (by omega)
        (by omega) (by omega)
  have hd : 0 ≤ ((i-m : ℕ) : ℚ) * ((-1 : ℚ)^m * tau (m+1) (i+2) r) -
      ((m+1 : ℕ) : ℚ) * ((-1 : ℚ)^(m+1) * tau (m+2) (i+2) r) := by
    have he : ((i-m : ℕ) : ℚ) * ((-1 : ℚ)^m * tau (m+1) (i+2) r) -
        ((m+1 : ℕ) : ℚ) * ((-1 : ℚ)^(m+1) * tau (m+2) (i+2) r) =
        ((i+1 : ℕ) : ℚ) * ((-1 : ℚ)^m * weightedCoeff (X*gPoly (m+1) (i+1)) (i+2) r) := by
      simp only [tau, pow_succ]
      linear_combination (-1 : ℚ)^m * hw
    rw [he]
    exact mul_nonneg (by positivity) hn
  have hc : (i.choose (m+1) : ℚ) * ((m+1 : ℕ) : ℚ) =
      (i.choose m : ℚ) * ((i-m : ℕ) : ℚ) := by
    exact_mod_cast Nat.choose_succ_right_eq i m
  have hp : 0 < (i.choose m : ℚ) := by exact_mod_cast Nat.choose_pos (by omega : m ≤ i)
  have hq : 0 < (i.choose (m+1) : ℚ) := by exact_mod_cast Nat.choose_pos (by omega : m+1 ≤ i)
  rw [div_le_div_iff₀ hq hp]
  have hh := mul_nonneg hp.le hd
  have hmpos : (0 : ℚ) < ((m+1 : ℕ) : ℚ) := by positivity
  apply (mul_le_mul_iff_right₀ hmpos).mp
  linear_combination hh - ((-1 : ℚ)^m * tau (m+1) (i+2) r) * hc

/-- The normalized signed coefficients decrease with the part-size parameter.
The conclusion holds for every coefficient index, without a restriction on `r`. -/
theorem normalized_tau_succ_le (m i r : ℕ) (hm : 1 ≤ m) (hi : m+1 < i) :
    ((-1 : ℚ)^m * tau (m+1) i r) / ((i-2).choose m : ℚ) ≤
      ((-1 : ℚ)^(m-1) * tau m i r) / ((i-2).choose (m-1) : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k+1 := ⟨m-1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ k, i = k+2 := ⟨i-2, by omega⟩
  simpa [Nat.add_assoc] using normalized_tau_succ_le_aux m i r (by omega)

/-- Monotonicity across an arbitrary interval of admissible part sizes. -/
theorem normalized_tau_antitone (p q i r : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) (hqi : q < i) :
    ((-1 : ℚ)^(q-1) * tau q i r) / ((i-2).choose (q-1) : ℚ) ≤
      ((-1 : ℚ)^(p-1) * tau p i r) / ((i-2).choose (p-1) : ℚ) := by
  revert hqi
  induction q, hpq using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ q hpq ih =>
    intro hqi
    have hs := normalized_tau_succ_le q i r (by omega) (by omega)
    exact le_trans (by simpa using hs) (ih (by omega))

end HilbertBipartite
