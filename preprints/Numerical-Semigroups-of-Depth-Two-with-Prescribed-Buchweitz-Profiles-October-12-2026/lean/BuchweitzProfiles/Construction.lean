import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.DivMod

/-! Parameters and quotient inequalities for the prescribed-profile construction. -/
namespace BuchweitzProfiles

/-- The number of large generators in the construction. -/
def largeCount (N L : ℤ) : ℤ := (N + 1)^2 + 2 * L * (N + 1)

/-- The Euclidean-division numerator at stage `n`. -/
def divisionNumerator (N L : ℤ) (a : ℤ → ℤ) (n : ℤ) : ℤ :=
  2 * largeCount N L + 5 - 2 * n + a n - a (n - 1)

/-- Quotients, including the specially prescribed first quotient. -/
def quotient (N L : ℤ) (a : ℤ → ℤ) (n : ℤ) : ℤ :=
  if n = 1 then largeCount N L else divisionNumerator N L a n / (2*n-1)

/-- Remainders in the Euclidean divisions. -/
def remainder (N L : ℤ) (a : ℤ → ℤ) (n : ℤ) : ℤ :=
  divisionNumerator N L a n % (2*n-1)

theorem largeCount_gt (N L : ℤ) (hN : 2 ≤ N) (hL : 1 ≤ L) :
    L + N < largeCount N L := by
  unfold largeCount
  nlinarith [mul_nonneg (show 0 ≤ L by omega) (show 0 ≤ N by omega)]

theorem divisionNumerator_pos (N L : ℤ) (a : ℤ → ℤ)
    (hN : 2 ≤ N) (hL : 1 ≤ L)
    (ha : ∀ k, 1 ≤ k → k ≤ N → -L ≤ a k ∧ a k ≤ L)
    (n : ℤ) (hn : 2 ≤ n) (hnN : n ≤ N) :
    0 < divisionNumerator N L a n := by
  have h := largeCount_gt N L hN hL
  obtain ⟨han, _⟩ := ha n (by omega) hnN
  obtain ⟨_, hap⟩ := ha (n-1) (by omega) (by omega)
  unfold divisionNumerator
  omega

theorem remainder_bounds (N L : ℤ) (a : ℤ → ℤ) (n : ℤ) (hn : 2 ≤ n) :
    0 ≤ remainder N L a n ∧ remainder N L a n ≤ 2*n-2 := by
  unfold remainder
  have hd : 0 < 2*n-1 := by omega
  exact ⟨Int.emod_nonneg _ (by omega), by have := Int.emod_lt_of_pos (divisionNumerator N L a n) hd; omega⟩

theorem division_identity (N L : ℤ) (a : ℤ → ℤ) (n : ℤ) (hn : 2 ≤ n) :
    (2*n-1) * quotient N L a n + remainder N L a n = divisionNumerator N L a n := by
  simp only [quotient, ite_eq_right (show n ≠ 1 by omega), remainder]
  exact Int.mul_ediv_add_emod _ _

/-- A gap of more than one between rational quotients gives strict floor decrease. -/
theorem quotient_strict_of_cross_gap (A B p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hgap : p*q < q*A-p*B) : B / q < A / p := by
  have hA := Int.lt_ediv_add_one_mul_self A hp
  have hB := Int.ediv_mul_le B (show q ≠ 0 by omega)
  by_contra h
  have hh : A / p ≤ B / q := by omega
  have hmul : (A / p) * p ≤ (B / q) * p := mul_le_mul_of_nonneg_right hh (by omega)
  have hA' : A < (B / q + 1)*p := by nlinarith
  have h1 := mul_lt_mul_of_pos_right hA' hq
  have h2 := mul_le_mul_of_nonneg_left hB (show 0 ≤ p by omega)
  nlinarith

theorem quotient_two_lt (N L : ℤ) (a : ℤ → ℤ)
    (hN : 2 ≤ N) (hL : 1 ≤ L) (ha1 : a 1 = 1) (ha2 : a 2 ≤ L) :
    quotient N L a 2 < quotient N L a 1 := by
  have hh := largeCount_gt N L hN hL
  simp only [quotient, show (2 : ℤ) ≠ 1 by omega, ite_false, ite_true]
  apply (Int.ediv_lt_iff_lt_mul (by norm_num : (0 : ℤ) < 2*2-1)).2
  norm_num [divisionNumerator, ha1]
  omega

theorem numerator_cross_gap (N L : ℤ) (a : ℤ → ℤ)
    (hN : 2 ≤ N) (hL : 1 ≤ L)
    (ha : ∀ k, 1 ≤ k → k ≤ N → -L ≤ a k ∧ a k ≤ L)
    (n : ℤ) (hn : 3 ≤ n) (hnN : n ≤ N) :
    (2*n-3)*(2*n-1) <
      (2*n-1)*divisionNumerator N L a (n-1) -
      (2*n-3)*divisionNumerator N L a n := by
  obtain ⟨hap, _⟩ := ha (n-1) (by omega) (by omega)
  obtain ⟨_, happ⟩ := ha (n-2) (by omega) (by omega)
  obtain ⟨_, han⟩ := ha n (by omega) hnN
  have e : n - 1 - 1 = n - 2 := by omega
  have h1 := mul_le_mul_of_nonneg_left hap (show 0 ≤ 4*n-4 by omega)
  have h2 := mul_le_mul_of_nonneg_left happ (show 0 ≤ 2*n-1 by omega)
  have h3 := mul_le_mul_of_nonneg_left han (show 0 ≤ 2*n-3 by omega)
  have h4 := mul_nonneg (show 0 ≤ L by omega) (show 0 ≤ N-n+2 by omega)
  have h5 := mul_nonneg (show 0 ≤ N+1-n by omega) (show 0 ≤ N+1+n by omega)
  unfold divisionNumerator largeCount
  rw [e]
  nlinarith

theorem quotient_decreasing (N L : ℤ) (a : ℤ → ℤ)
    (hN : 2 ≤ N) (hL : 1 ≤ L)
    (ha : ∀ k, 1 ≤ k → k ≤ N → -L ≤ a k ∧ a k ≤ L)
    (n : ℤ) (hn : 3 ≤ n) (hnN : n ≤ N) :
    quotient N L a n < quotient N L a (n-1) := by
  simp only [quotient, ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n-1 ≠ 1 by omega)]
  convert quotient_strict_of_cross_gap
    (divisionNumerator N L a (n-1)) (divisionNumerator N L a n)
    (2*n-3) (2*n-1) (by omega) (by omega)
    (numerator_cross_gap N L a hN hL ha n hn hnN) using 1
  congr 1
  ring

theorem quotient_nonnegative (N L : ℤ) (a : ℤ → ℤ)
    (hN : 2 ≤ N) (hL : 1 ≤ L)
    (ha : ∀ k, 1 ≤ k → k ≤ N → -L ≤ a k ∧ a k ≤ L)
    (n : ℤ) (hn : 2 ≤ n) (hnN : n ≤ N) :
    0 ≤ quotient N L a n := by
  rw [quotient, ite_eq_right (show n ≠ 1 by omega)]
  exact Int.ediv_nonneg (le_of_lt (divisionNumerator_pos N L a hN hL ha n hn hnN)) (by omega)

/-- Positional arithmetic used for the small generators. -/
def digitUnit (K M : ℤ) : ℤ := (2*K+1)*M

/-- Distance of a large generator from the truncation endpoint. -/
def digitRho (K M d t j : ℤ) : ℤ :=
  (d-1)*digitUnit K M + (t-1)*M+j

/-- The exact three-way cutoff in Proposition 4.3. -/
theorem digit_cutoff (K M d t j l b : ℤ)
    (hK : d ≤ K) (hM : 0 < M) (hd : 2 ≤ d)
    (ht0 : 0 ≤ t) (ht : t ≤ 2*d-2)
    (hj0 : 0 < j) (hj : j < M)
    (hl : 0 ≤ l) (hb0 : 0 ≤ b) (hb : b ≤ 2*l) :
    l*digitUnit K M+b*M ≤ digitRho K M d t j ↔
      l ≤ d-2 ∨ (l = d-1 ∧ b < t) := by
  have hK0 : 0 ≤ K := by omega
  unfold digitUnit digitRho
  simp only [digitUnit]
  constructor
  · intro h
    by_cases hlow : l ≤ d-2
    · exact Or.inl hlow
    have hld : d-1 ≤ l := by omega
    have hdiff := mul_nonneg (show 0 ≤ l-(d-1) by omega) hM.le
    have hbase := mul_nonneg hb0 hM.le
    have htM := mul_le_mul_of_nonneg_right ht hM.le
    by_cases heq : l = d-1
    · right; refine ⟨heq, ?_⟩
      subst l
      have : (b-t+1)*M ≤ j := by nlinarith
      by_contra hn
      have hprod := mul_le_mul_of_nonneg_right (show 1 ≤ b-t+1 by omega) hM.le
      nlinarith
    · have hdl : d ≤ l := by omega
      have hprod := mul_nonneg (show 0 ≤ l-d by omega)
        (show 0 ≤ (2*K+1)*M by positivity)
      have hKM := mul_nonneg (show 0 ≤ K-d by omega) hM.le
      nlinarith
  · rintro (hlow | ⟨rfl, hbt⟩)
    · have h1 := mul_nonneg (show 0 ≤ d-2-l by omega)
        (show 0 ≤ (2*K+1)*M by positivity)
      have h2 := mul_le_mul_of_nonneg_right hb hM.le
      have h3 := mul_nonneg ht0 hM.le
      have h4 := mul_nonneg (show 0 ≤ K-l by omega) hM.le
      nlinarith
    · have h1 := mul_le_mul_of_nonneg_right (show b ≤ t-1 by omega) hM.le
      nlinarith

theorem digitRho_bounds (N M d t j : ℤ) (hN : 2 ≤ N) (hM : 0 < M)
    (hd : 2 ≤ d) (hdN : d ≤ N+1) (ht0 : 0 ≤ t) (ht : t ≤ 2*d-2)
    (hj0 : 0 < j) (hj : j < M) :
    0 < digitRho (2*N+2) M d t j ∧
      digitRho (2*N+2) M d t j ≤ N*(digitUnit (2*N+2) M+2*M)-1 := by
  have hU : 0 < digitUnit (2*N+2) M := by unfold digitUnit; positivity
  have h1 := mul_le_mul_of_nonneg_right (show 1 ≤ d-1 by omega) hU.le
  have h2 := mul_le_mul_of_nonneg_right (show d-1 ≤ N by omega) hU.le
  have h3 := mul_nonneg ht0 hM.le
  have h4 := mul_le_mul_of_nonneg_right (show t-1 ≤ 2*N-1 by omega) hM.le
  have h5 := mul_nonneg (show 0 ≤ N by omega) hM.le
  unfold digitRho digitUnit at *
  constructor <;> nlinarith

/-- The large generators are above half the cutoff and have nonzero digit residues. -/
theorem large_generator_bounds (N M d t j : ℤ) (hN : 2 ≤ N) (hM : 0 < M)
    (hd : 2 ≤ d) (hdN : d ≤ N+1) (ht0 : 0 ≤ t) (ht : t ≤ 2*d-2)
    (hj0 : 0 < j) (hj : j < M) :
    let u := digitUnit (2*N+2) M
    let m := (2*N+2)*(u+2*M)+1
    let v := m-1-digitRho (2*N+2) M d t j
    (N+2)*(u+2*M) < v ∧ v ≤ m-2 ∧ m < 2*v := by
  obtain ⟨hlo, hhi⟩ := digitRho_bounds N M d t j hN hM hd hdN ht0 ht hj0 hj
  have hu : 0 < digitUnit (2*N+2) M := by unfold digitUnit; positivity
  dsimp
  constructor
  · nlinarith
  constructor
  · omega
  · nlinarith

end BuchweitzProfiles
