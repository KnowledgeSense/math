import HilbertBipartite.CorrectionIdentity
import Mathlib.Tactic.LinearCombination
import HilbertBipartite.SquareCoefficients

open Finset Polynomial
namespace HilbertBipartite

@[simp] theorem delta_zero_left (i : ℕ) (hi : 1 ≤ i) :
    delta 0 i = (X : Polynomial ℚ)^(i-1) := by
  simpa [delta] using full_binomial_numerator i hi

theorem delta_eq_zero_if_index_le (m i : ℕ) (hi : i ≤ m) : delta m i = 0 := by
  unfold delta
  apply sum_eq_zero
  intro j hj
  have h := mem_filter.mp hj
  have := mem_range.mp h.1
  omega

private theorem partial_numerator_pascal (a N : ℕ) :
    (∑ j ∈ range (a+1), C ((-1 : ℚ)^j * ((N+1).choose j : ℚ)) * (1-X)^j) =
      (∑ j ∈ range (a+1), C ((-1 : ℚ)^j * (N.choose j : ℚ)) * (1-X)^j) -
        (1-X) * ∑ j ∈ range a, C ((-1 : ℚ)^j * (N.choose j : ℚ)) * (1-X)^j := by
  rw [sum_range_succ', sum_range_succ' (fun j =>
    C ((-1 : ℚ)^j * (N.choose j : ℚ)) * (1-X)^j)]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, map_one]
  simp_rw [Nat.choose_succ_succ, Nat.cast_add, mul_add, map_add, add_mul]
  rw [sum_add_distrib, mul_sum]
  have hs : (∑ j ∈ range a,
      C ((-1 : ℚ)^(j+1) * (N.choose j : ℚ)) * (1-X)^(j+1)) =
      - ∑ j ∈ range a, (1-X) * (C ((-1 : ℚ)^j * (N.choose j : ℚ)) * (1-X)^j) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j _
    rw [pow_succ, pow_succ]
    simp only [mul_neg_one, neg_mul, map_neg]
    ring
  rw [hs]
  ring

theorem delta_pascal (a i : ℕ) (hi : 1 ≤ i) (ha : a+1 ≤ i) :
    delta (a+1) (i+1) = delta (a+1) i - (1-X) * delta a i := by
  have h0 := gPoly_partial (a+1) (i+1) (by omega) (by omega)
  have h1 := gPoly_partial (a+1) i hi ha
  have h2 := gPoly_partial a i hi (by omega)
  unfold gPoly at h0 h1 h2
  rw [show i+1-1=i by omega] at h0
  have hp := partial_numerator_pascal a (i-1)
  rw [show i-1+1=i by omega] at hp
  rw [← h0, ← h1, ← h2] at hp
  have he : (X : Polynomial ℚ)^i = X^(i-1)*X := by
    conv_lhs => rw [show i=i-1+1 by omega, pow_succ]
  rw [he] at hp
  linear_combination -hp

/-- Signed tail polynomial, indexed by its distance from the first nonzero coefficient. -/
noncomputable def signedDelta (a d : ℕ) : Polynomial ℚ :=
  C ((-1 : ℚ)^a) * delta a (a+d+1)

theorem signedDelta_pascal (a d : ℕ) :
    signedDelta (a+1) (d+1) = signedDelta (a+1) d + (1-X) * signedDelta a (d+1) := by
  unfold signedDelta
  have hp := delta_pascal a (a+d+2) (by omega) (by omega)
  have hsign : C ((-1 : ℚ)^(a+1)) = -C ((-1 : ℚ)^a) := by simp [pow_succ]
  simp only [show a+1+(d+1)+1=(a+d+2)+1 by omega,
    show a+1+d+1=a+d+2 by omega, show a+(d+1)+1=a+d+2 by omega,
    hsign, hp]
  ring

theorem signedDelta_zero (a : ℕ) : signedDelta a 0 = (1-X)^a := by
  unfold signedDelta delta
  have hf : (range (a+0+1)).filter (a ≤ ·) = {a} := by
    ext j
    simp only [mem_filter, mem_range, mem_singleton]
    omega
  rw [hf]
  simp only [sum_singleton, Nat.add_zero, Nat.add_sub_cancel, Nat.choose_self,
    Nat.cast_one, mul_one]
  rw [← mul_assoc, ← map_mul, ← pow_add, ← two_mul, pow_mul]
  norm_num

@[simp] theorem signedDelta_zero_left (d : ℕ) : signedDelta 0 d = X^d := by
  simp [signedDelta, delta_zero_left]

/-- The proposed coefficient of `P_{b,a}(1+X)`, with negative extraction indices zero. -/
noncomputable def correctionCandidate (a b d : ℕ) : ℚ :=
  if d+2 ≤ b then weightedCoeff (signedDelta a d) (a+d+1) (b-d-2) else 0

@[simp] theorem correctionCandidate_zero (a d : ℕ) : correctionCandidate a 0 d = 0 := by
  simp [correctionCandidate]

@[simp] theorem correctionCandidate_one (a d : ℕ) : correctionCandidate a 1 d = 0 := by
  simp [correctionCandidate]

theorem weightedCoeff_one_sub_X_mul_succ (P : Polynomial ℚ) (i r : ℕ) :
    weightedCoeff ((1-X)*P) i (r+1) = weightedCoeff P i (r+1) - weightedCoeff P i r := by
  rw [sub_mul, one_mul, weightedCoeff_sub, weightedCoeff_X_mul_succ]

theorem correctionCandidate_succ_succ (a b d : ℕ) :
    correctionCandidate (a+1) (b+1) (d+1) =
      correctionCandidate a (b+1) (d+1) + 2*correctionCandidate (a+1) b (d+1) +
        correctionCandidate (a+1) b d - correctionCandidate a b (d+1) := by
  by_cases h : d+3 ≤ b
  · have h1 : d+1+2 ≤ b+1 := by omega
    have h2 : d+1+2 ≤ b := by omega
    have h3 : d+2 ≤ b := by omega
    unfold correctionCandidate
    rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left h2, ite_eq_left h3, ite_eq_left h2]
    have he1 : b+1-(d+1)-2 = (b-d-3)+1 := by omega
    have he2 : b-(d+1)-2 = b-d-3 := by omega
    have he3 : b-d-2 = (b-d-3)+1 := by omega
    rw [he1, he2, he3]
    have hp := weightedCoeff_pascal (signedDelta (a+1) (d+1)) (a+d+2) (b-d-3)
    rw [show a+1+(d+1)+1=a+d+2+1 by omega,
      show a+(d+1)+1=a+d+2 by omega,
      show a+1+d+1=a+d+2 by omega]
    conv_rhs at hp =>
      rw [signedDelta_pascal, weightedCoeff_add, weightedCoeff_one_sub_X_mul_succ]
    linarith
  · by_cases hb : b=d+2
    · subst b
      have h1 : d+1+2 ≤ d+2+1 := by omega
      have h2 : ¬ d+1+2 ≤ d+2 := by omega
      unfold correctionCandidate
      rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right h2, ite_eq_left (le_refl _), ite_eq_right h2]
      simp only [show d+2+1-(d+1)-2=0 by omega, show d+2-d-2=0 by omega,
        weightedCoeff_zero_degree, mul_zero, add_zero, sub_zero]
      rw [signedDelta_pascal]
      simp [sub_mul, add_comm]
    · have h1 : ¬ d+1+2 ≤ b+1 := by omega
      have h2 : ¬ d+1+2 ≤ b := by omega
      have h3 : ¬ d+2 ≤ b := by omega
      simp [correctionCandidate, h1, h2, h3]

theorem correctionCandidate_succ_zero (a b : ℕ) :
    correctionCandidate (a+1) (b+1) 0 =
      correctionCandidate a (b+1) 0 + 2*correctionCandidate (a+1) b 0 -
        correctionCandidate a b 0 := by
  by_cases hb : 2 ≤ b
  · unfold correctionCandidate
    simp only [Nat.zero_add, Nat.sub_zero, ite_eq_left hb, ite_eq_left (by omega : 2 ≤ b+1),
      Nat.add_zero, signedDelta_zero]
    rw [show b+1-2=(b-2)+1 by omega]
    have hp := weightedCoeff_pascal ((1-X)^(a+1)) (a+1) (b-2)
    conv_rhs at hp => rw [pow_succ', weightedCoeff_one_sub_X_mul_succ]
    linarith
  · have hb : b=0 ∨ b=1 := by omega
    rcases hb with rfl | rfl
    · simp
    · simp [correctionCandidate, signedDelta_zero, coeff_zero_eq_eval_zero]

theorem weightedCoeff_X_pow_all (d i r : ℕ) :
    weightedCoeff (X^d) i r =
      if d ≤ r then 2^(r-d) * ((r-d+i).choose i : ℚ) else 0 := by
  classical
  simp only [weightedCoeff, coeff_X_pow, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq', mem_range]
  split_ifs <;> rename_i h1 h2 <;> first | rfl | omega

theorem correctionCandidate_zero_left (b d : ℕ) :
    correctionCandidate 0 b d = (squareCoefficient b (d+1) : ℚ) := by
  unfold correctionCandidate
  rw [signedDelta_zero_left]
  by_cases h : d+2 ≤ b
  · rw [ite_eq_left h, weightedCoeff_X_pow_all]
    by_cases hd : d ≤ b-d-2
    · rw [ite_eq_left hd]
      unfold squareCoefficient
      have he1 : b-d-2-d=b-2*(d+1) := by omega
      have he2 : b-d-2-d+(0+d+1)=b-(d+1) := by omega
      rw [he2, he1]
      push_cast
      simp only [Nat.zero_add]
    · rw [ite_eq_right hd, squareCoefficient_eq_zero b (d+1) (by omega)]
      rfl
  · rw [ite_eq_right h, squareCoefficient_eq_zero b (d+1) (by omega)]
    rfl

theorem correctionCandidate_base_succ (b d : ℕ) :
    correctionCandidate 0 (b+2) (d+1) =
      2*correctionCandidate 0 (b+1) (d+1) + correctionCandidate 0 b d := by
  simp only [correctionCandidate_zero_left, squareCoefficient_recurrence]
  push_cast
  rfl

theorem correctionCandidate_base_zero (b : ℕ) :
    correctionCandidate 0 (b+2) 0 = 2*correctionCandidate 0 (b+1) 0 + 2^b := by
  simp only [correctionCandidate_zero_left, squareCoefficient_recurrence,
    squareCoefficient_zero_index]
  push_cast
  rfl

end HilbertBipartite
