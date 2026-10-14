import HilbertBipartite.TauMonotonicity

open Finset Polynomial

namespace HilbertBipartite

theorem delta_eq_zero_of_le (m i : ℕ) (h : i ≤ m) : delta m i = 0 := by
  unfold delta
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hj, hmj⟩ := Finset.mem_filter.mp hj
  have := Finset.mem_range.mp hj
  omega

theorem weightedCoeff_X_pow_eq_zero (k i r : ℕ) (h : r < k) :
    weightedCoeff ((X : Polynomial ℚ)^k) i r = 0 := by
  unfold weightedCoeff
  apply Finset.sum_eq_zero
  intro j hj
  rw [Polynomial.coeff_X_pow, ite_eq_right]
  · simp
  · have := Finset.mem_range.mp hj
    omega

theorem coefficientFormula_eq_tau_of_le (p q i : ℕ)
    (hp : p < i) (hi : i < p+q) (hiq : i ≤ q) :
    coefficientFormula p q i = tau p i (p+q-i-1) := by
  rw [coefficientFormula, ite_eq_right (by omega), ite_eq_left hi,
    delta_eq_zero_of_le q i hiq, sub_zero]
  rfl

theorem coefficientFormula_eq_tau_add (p q i : ℕ)
    (hpq : p ≤ q) (hq : q < i) (hi : i < p+q) :
    coefficientFormula p q i = tau p i (p+q-i-1) + tau q i (p+q-i-1) := by
  have hpow := weightedCoeff_X_pow_eq_zero (i-1) i (p+q-i-1) (by omega)
  rw [coefficientFormula, ite_eq_right (by omega), ite_eq_left hi]
  have he : (X : Polynomial ℚ)^(i-1)-delta p i-delta q i =
      gPoly p i + gPoly q i - X^(i-1) := by unfold gPoly; ring
  rw [he, weightedCoeff_sub, weightedCoeff_add, hpow, sub_zero]
  rfl

theorem neg_one_pow_add_two (p : ℕ) (hp : 1 ≤ p) :
    (-1 : ℚ)^(p+1) = (-1 : ℚ)^(p-1) := by
  rw [show p+1 = (p-1)+2 by omega, pow_add]
  norm_num

theorem coefficientFormula_signed_pos_of_le (p q i : ℕ)
    (hp : 1 ≤ p) (hpi : p < i) (hi : i < p+q) (hiq : i ≤ q) :
    0 < (-1 : ℚ)^(p+1)*coefficientFormula p q i := by
  rw [coefficientFormula_eq_tau_of_le p q i hpi hi hiq, neg_one_pow_add_two p hp]
  exact signed_tau_pos p i (p+q-i-1) hp hpi

theorem coefficientFormula_signed_pos_of_same_sign (p q i : ℕ)
    (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q < i) (hi : i < p+q)
    (he : (-1 : ℚ)^(p-1) = (-1 : ℚ)^(q-1)) :
    0 < (-1 : ℚ)^(p+1)*coefficientFormula p q i := by
  rw [coefficientFormula_eq_tau_add p q i hpq hq hi, neg_one_pow_add_two p hp, mul_add]
  have h1 := signed_tau_pos p i (p+q-i-1) hp (by omega)
  have h2 := signed_tau_pos q i (p+q-i-1) (by omega) hq
  rw [← he] at h2
  exact add_pos h1 h2

theorem choose_lt_succ_below_half (N k : ℕ) (h : 2*k+1 < N) :
    N.choose k < N.choose (k+1) := by
  have hp := Nat.choose_pos (by omega : k ≤ N)
  have he := Nat.choose_succ_right_eq N k
  have hk : k+1 < N-k := by omega
  nlinarith

theorem choose_le_choose_below_half (N a b : ℕ) (hab : a ≤ b) (hb : 2*b ≤ N) :
    N.choose a ≤ N.choose b := by
  induction b with
  | zero =>
    have ha : a=0 := by omega
    simp [ha]
  | succ b ih =>
    by_cases he : a=b+1
    · simp [he]
    · have h1 := ih (by omega) (by omega)
      have h2 := Nat.choose_le_succ_of_lt_half_left (n:=N) (r:=b) (by omega)
      exact h1.trans h2

theorem choose_lt_choose_below_half (N a b : ℕ) (hab : a < b) (hb : 2*b ≤ N) :
    N.choose a < N.choose b := by
  have h1 := choose_lt_succ_below_half N a (by omega)
  have h2 := choose_le_choose_below_half N (a+1) b (by omega) hb
  exact h1.trans_le h2

theorem choose_strict_between_symmetric (N a b : ℕ)
    (hba : b < a) (hab : a < N-b) : N.choose b < N.choose a := by
  by_cases ha : 2*a ≤ N
  · exact choose_lt_choose_below_half N b a hba ha
  · rw [← Nat.choose_symm (show a ≤ N by omega)]
    exact choose_lt_choose_below_half N b (N-a) (by omega) (by omega)

theorem high_index_choose_dominance (p q i : ℕ)
    (hp : 1 ≤ p) (hpq : p < q) (hq : q < i) (hi : i < p+q) :
    (i-2).choose (q-1) < (i-2).choose (p-1) := by
  rw [← Nat.choose_symm (show q-1 ≤ i-2 by omega)]
  apply choose_strict_between_symmetric
  · omega
  · omega

theorem weightedCoeff_X_pow (k i r : ℕ) (h : k ≤ r) :
    weightedCoeff ((X : Polynomial ℚ)^k) i r =
      2^(r-k) * ((r-k+i).choose i : ℚ) := by
  classical
  simp [weightedCoeff, Polynomial.coeff_X_pow, Finset.sum_ite_eq', h]

theorem coefficientFormula_low (p q i : ℕ)
    (hp : 1 ≤ p) (hpq : p ≤ q) (hi : i ≤ p) :
    coefficientFormula p q i = 2^(p+q-2*i) * ((p+q-i).choose i : ℚ) := by
  by_cases hi0 : i=0
  · simp [coefficientFormula, hi0]
  · rw [coefficientFormula, ite_eq_right hi0, ite_eq_left (by omega),
      delta_eq_zero_of_le p i hi, delta_eq_zero_of_le q i (by omega), sub_zero, sub_zero,
      weightedCoeff_X_pow (i-1) i (p+q-i-1) (by omega)]
    rw [show p+q-i-1-(i-1) = p+q-2*i by omega,
      show p+q-2*i+i = p+q-i by omega]

theorem coefficientFormula_low_pos (p q i : ℕ)
    (hp : 1 ≤ p) (hpq : p ≤ q) (hi : i ≤ p) :
    0 < coefficientFormula p q i := by
  rw [coefficientFormula_low p q i hp hpq hi]
  apply mul_pos (by positivity)
  exact_mod_cast Nat.choose_pos (by omega : i ≤ p+q-i)

theorem coefficientFormula_eq_zero_of_ge (p q i : ℕ) (hp : 1 ≤ p) (hi : p+q ≤ i) :
    coefficientFormula p q i = 0 := by
  simp [coefficientFormula, show i ≠ 0 by omega, show ¬ i < p+q by omega]

theorem signed_tau_strict_dominance_of_normalized (p q i r : ℕ)
    (hp : 1 ≤ p) (hpq : p < q) (hq : q < i) (hi : i < p+q)
    (hm : ((-1 : ℚ)^(q-1)*tau q i r) / ((i-2).choose (q-1) : ℚ) ≤
      ((-1 : ℚ)^(p-1)*tau p i r) / ((i-2).choose (p-1) : ℚ)) :
    (-1 : ℚ)^(q-1)*tau q i r < (-1 : ℚ)^(p-1)*tau p i r := by
  have hcp : 0 < ((i-2).choose (p-1) : ℚ) := by
    exact_mod_cast Nat.choose_pos (by omega : p-1 ≤ i-2)
  have hcq : 0 < ((i-2).choose (q-1) : ℚ) := by
    exact_mod_cast Nat.choose_pos (by omega : q-1 ≤ i-2)
  have hcmp : ((i-2).choose (q-1) : ℚ) < ((i-2).choose (p-1) : ℚ) := by
    exact_mod_cast high_index_choose_dominance p q i hp hpq hq hi
  have hpos := signed_tau_pos q i r (by omega) hq
  have hcross := (div_le_div_iff₀ hcq hcp).mp hm
  have hmul := mul_lt_mul_of_pos_left hcmp hpos
  exact lt_of_mul_lt_mul_right (hmul.trans_le hcross) (le_of_lt hcq)

theorem coefficientFormula_signed_pos_of_opposite_sign (p q i : ℕ)
    (hp : 1 ≤ p) (hpq : p < q) (hq : q < i) (hi : i < p+q)
    (he : (-1 : ℚ)^(p-1) = -(-1 : ℚ)^(q-1))
    (hm : ((-1 : ℚ)^(q-1)*tau q i (p+q-i-1)) / ((i-2).choose (q-1) : ℚ) ≤
      ((-1 : ℚ)^(p-1)*tau p i (p+q-i-1)) / ((i-2).choose (p-1) : ℚ)) :
    0 < (-1 : ℚ)^(p+1)*coefficientFormula p q i := by
  have hd := signed_tau_strict_dominance_of_normalized p q i (p+q-i-1) hp hpq hq hi hm
  rw [coefficientFormula_eq_tau_add p q i (by omega) hq hi,
    neg_one_pow_add_two p hp, mul_add]
  have heq : (-1 : ℚ)^(p-1)*tau q i (p+q-i-1) =
      -((-1 : ℚ)^(q-1)*tau q i (p+q-i-1)) := by rw [he, neg_mul]
  rw [heq]
  linarith

theorem coefficientFormula_high_signed_pos (p q i : ℕ)
    (hp : 1 ≤ p) (hpq : p ≤ q) (hpi : p < i) (hi : i < p+q) :
    0 < (-1 : ℚ)^(p+1)*coefficientFormula p q i := by
  by_cases hq : i ≤ q
  · exact coefficientFormula_signed_pos_of_le p q i hp hpi hi hq
  · have hqi : q < i := by omega
    by_cases he : (-1 : ℚ)^(p-1) = (-1 : ℚ)^(q-1)
    · exact coefficientFormula_signed_pos_of_same_sign p q i hp hpq hqi hi he
    · have hpqlt : p < q := by
        by_contra hh
        have hpqe : p=q := by omega
        exact he (by rw [hpqe])
      have heopp : (-1 : ℚ)^(p-1) = -(-1 : ℚ)^(q-1) := by
        rcases neg_one_pow_eq_or ℚ (p-1) with h1 | h1
        · rcases neg_one_pow_eq_or ℚ (q-1) with h2 | h2
          · exact False.elim (he (h1.trans h2.symm))
          · rw [h1, h2]; norm_num
        · rcases neg_one_pow_eq_or ℚ (q-1) with h2 | h2
          · rw [h1, h2]
          · exact False.elim (he (h1.trans h2.symm))
      apply coefficientFormula_signed_pos_of_opposite_sign p q i hp hpqlt hqi hi heopp
      exact normalized_tau_antitone p q i (p+q-i-1) hp hpq hqi

theorem coefficientFormula_high_ne_zero (p q i : ℕ)
    (hp : 1 ≤ p) (hpq : p ≤ q) (hpi : p < i) (hi : i < p+q) :
    coefficientFormula p q i ≠ 0 := by
  have hs := coefficientFormula_high_signed_pos p q i hp hpq hpi hi
  intro he
  rw [he, mul_zero] at hs
  exact (lt_irrefl 0) hs

theorem coefficientFormula_high_pos_of_odd (p q i : ℕ)
    (hp : 1 ≤ p) (hpq : p ≤ q) (hpi : p < i) (hi : i < p+q) (ho : Odd p) :
    0 < coefficientFormula p q i := by
  have hs := coefficientFormula_high_signed_pos p q i hp hpq hpi hi
  simpa only [ho.add_one.neg_one_pow, one_mul] using hs

theorem coefficientFormula_high_neg_of_even (p q i : ℕ)
    (hp : 1 ≤ p) (hpq : p ≤ q) (hpi : p < i) (hi : i < p+q) (he : Even p) :
    coefficientFormula p q i < 0 := by
  have hs := coefficientFormula_high_signed_pos p q i hp hpq hpi hi
  rw [he.add_one.neg_one_pow, neg_one_mul] at hs
  linarith

theorem coefficientFormula_all_nonneg_iff (p q : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) :
    (∀ i : ℕ, 0 ≤ coefficientFormula p q i) ↔ Odd p := by
  constructor
  · intro hn
    by_contra ho
    have he := Nat.not_odd_iff_even.mp ho
    have hp2 : 2 ≤ p := by have := Nat.even_iff.mp he; omega
    have hneg := coefficientFormula_high_neg_of_even p q (p+1) hp hpq (by omega)
      (by omega) he
    exact (not_lt_of_ge (hn (p+1))) hneg
  · intro ho i
    by_cases hip : i ≤ p
    · exact (coefficientFormula_low_pos p q i hp hpq hip).le
    · by_cases hi : i < p+q
      · exact (coefficientFormula_high_pos_of_odd p q i hp hpq (by omega) hi ho).le
      · rw [coefficientFormula_eq_zero_of_ge p q i hp (by omega)]

theorem coefficientFormula_nonneg_iff (p q : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) :
    (∀ i ≤ p+q, 0 ≤ coefficientFormula p q i) ↔ Odd p := by
  rw [← coefficientFormula_all_nonneg_iff p q hp hpq]
  constructor
  · intro h i
    by_cases hi : i ≤ p+q
    · exact h i hi
    · rw [coefficientFormula_eq_zero_of_ge p q i hp (by omega)]
  · intro h i _
    exact h i

end HilbertBipartite
