import Fan.DelannoyRoots

noncomputable section
open Polynomial
open scoped BigOperators
namespace Fan

/-- The polynomial obtained after removing the endpoint factor in Rodrigues's formula. -/
def jacobiAux (a b : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (a+1), C ((a.choose k : ℝ) * b.choose k) * X^k * (X+C 1)^(a-k)

private theorem factorial_product (a b k : ℕ) (hk : k ≤ a) :
    a.choose k * a.descFactorial (a-k) * b.descFactorial k =
      a.factorial * (a.choose k * b.choose k) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose b k]
  have h := Nat.factorial_mul_descFactorial (Nat.sub_le a k)
  rw [Nat.sub_sub_self hk] at h
  calc
    a.choose k * a.descFactorial (a-k) * (k.factorial * b.choose k) =
      (k.factorial * a.descFactorial (a-k)) * (a.choose k * b.choose k) := by ring
    _ = _ := by rw [h]

/-- Rodrigues's identity with its exact normalization and endpoint factor. -/
theorem delannoy_rodrigues (a b : ℕ) (hab : a ≤ b) :
    derivative^[a] ((X : Polynomial ℝ)^a * (X+C 1)^b) =
      C (a.factorial : ℝ) * (X+C 1)^(b-a) * jacobiAux a b := by
  rw [iterate_derivative_mul]
  unfold jacobiAux
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hka : k ≤ a := by simpa using Finset.mem_range.mp hk
  have hkb : k ≤ b := hka.trans hab
  rw [iterate_derivative_X_pow_eq_C_mul, iterate_derivative_X_add_pow]
  have hsub : a-(a-k)=k := Nat.sub_sub_self hka
  have hpow : b-k=(b-a)+(a-k) := by omega
  rw [hsub, hpow, pow_add]
  have hcoef : (a.choose k : ℝ) * a.descFactorial (a-k) * b.descFactorial k =
      (a.factorial : ℝ) * ((a.choose k : ℝ) * b.choose k) := by
    exact_mod_cast factorial_product a b k hka
  simp only [nsmul_eq_mul, ← C_eq_natCast]
  calc
    C (a.choose k : ℝ) * (C (a.descFactorial (a-k) : ℝ) * X^k *
        (C (b.descFactorial k : ℝ) * ((X+C 1)^(b-a) * (X+C 1)^(a-k)))) =
      C ((a.choose k : ℝ) * a.descFactorial (a-k) * b.descFactorial k) *
        (X+C 1)^(b-a) * X^k * (X+C 1)^(a-k) := by simp only [map_mul]; ring
    _ = _ := by rw [hcoef]; simp only [map_mul]; ring

@[simp] theorem jacobiAux_eval_zero (a b : ℕ) : (jacobiAux a b).eval 0 = 1 := by
  simp [jacobiAux, eval_finsetSum, zero_pow_eq]

theorem jacobiAux_ne_zero (a b : ℕ) : jacobiAux a b ≠ 0 := by
  intro h
  have := jacobiAux_eval_zero a b
  simp [h] at this

theorem real_splits_iterate_derivative {p : Polynomial ℝ} (hp : p.Splits) (k : ℕ) :
    (derivative^[k] p).Splits := by
  induction k with
  | zero => simpa using hp
  | succ k ih => simpa only [Function.iterate_succ_apply'] using real_splits_derivative ih

theorem jacobiAux_splits (a b : ℕ) (hab : a ≤ b) : (jacobiAux a b).Splits := by
  have hp : ((X : Polynomial ℝ)^a * (X+C 1)^b).Splits := by
    exact (Splits.X.pow a).mul ((Splits.X_add_C (1:ℝ)).pow b)
  have hd := real_splits_iterate_derivative hp a
  rw [delannoy_rodrigues a b hab] at hd
  apply hd.of_dvd
  · exact mul_ne_zero (mul_ne_zero (by simpa using (Nat.factorial_ne_zero a))
      (pow_ne_zero _ (monic_X_add_C (1:ℝ)).ne_zero)) (jacobiAux_ne_zero a b)
  · exact dvd_mul_left _ _

theorem jacobiAux_eval_neg_one (a b : ℕ) :
    (jacobiAux a b).eval (-1) = (b.choose a : ℝ) * (-1)^a := by
  unfold jacobiAux
  rw [eval_finsetSum, Finset.sum_eq_single a]
  · simp
  · intro k hk hka
    have hklt : k < a := by have := Finset.mem_range.mp hk; omega
    simp [show a-k ≠ 0 by omega]
  · simp

theorem jacobiAux_eval_neg_one_ne_zero (a b : ℕ) (hab : a ≤ b) :
    (jacobiAux a b).eval (-1) ≠ 0 := by
  rw [jacobiAux_eval_neg_one]
  exact mul_ne_zero (by exact_mod_cast (Nat.choose_pos hab).ne') (pow_ne_zero _ (by norm_num))

theorem real_iterate_derivative_roots_in_interval {p : Polynomial ℝ} (hp : p.Splits)
    {a b : ℝ} (hr : ∀ x ∈ p.roots, a ≤ x ∧ x ≤ b) (k : ℕ) :
    ∀ x ∈ (derivative^[k] p).roots, a ≤ x ∧ x ≤ b := by
  induction k with
  | zero => simpa using hr
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using
      real_derivative_roots_in_interval (real_splits_iterate_derivative hp k) ih

/-- Every root of the Rodrigues quotient lies strictly between its endpoints. -/
theorem jacobiAux_roots_interval (a b : ℕ) (hab : a ≤ b) :
    ∀ x ∈ (jacobiAux a b).roots, -1 < x ∧ x < 0 := by
  let p : Polynomial ℝ := X^a * (X+C 1)^b
  have hp : p.Splits := (Splits.X.pow a).mul ((Splits.X_add_C (1:ℝ)).pow b)
  have hp0 : p ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero)
    (pow_ne_zero _ (monic_X_add_C (1:ℝ)).ne_zero)
  have hr : ∀ x ∈ p.roots, -1 ≤ x ∧ x ≤ 0 := by
    intro x hx
    have he : x^a * (x+1)^b = 0 := by
      simpa [p, IsRoot] using (mem_roots hp0).mp hx
    rcases mul_eq_zero.mp he with h | h
    · have := eq_zero_of_pow_eq_zero h
      constructor <;> linarith
    · have := eq_zero_of_pow_eq_zero h
      constructor <;> linarith
  have hfac := delannoy_rodrigues a b hab
  have hder : derivative^[a] p ≠ 0 := by
    rw [show p = X^a * (X+C 1)^b from rfl,hfac]
    exact mul_ne_zero (mul_ne_zero (by simpa using (Nat.factorial_ne_zero a))
      (pow_ne_zero _ (monic_X_add_C (1:ℝ)).ne_zero)) (jacobiAux_ne_zero a b)
  intro x hx
  have he : (jacobiAux a b).eval x = 0 := (mem_roots (jacobiAux_ne_zero a b)).mp hx
  have hdx : x ∈ (derivative^[a] p).roots := by
    apply (mem_roots hder).mpr
    change (derivative^[a] (X^a * (X+C 1)^b)).eval x = 0
    rw [hfac]
    simp [he]
  have hbds := real_iterate_derivative_roots_in_interval hp hr a x hdx
  have hx0 : x ≠ 0 := by intro h; subst x; simp at he
  have hxm : x ≠ -1 := by intro h; subst x; exact jacobiAux_eval_neg_one_ne_zero a b hab he
  exact ⟨lt_of_le_of_ne hbds.1 (Ne.symm hxm),lt_of_le_of_ne hbds.2 hx0⟩

theorem real_natDegree_iterate_derivative (p : Polynomial ℝ) (k : ℕ) :
    (derivative^[k] p).natDegree = p.natDegree-k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply',natDegree_derivative,ih]; omega

theorem jacobiAux_natDegree (a b : ℕ) (hab : a ≤ b) : (jacobiAux a b).natDegree = a := by
  have h := congrArg Polynomial.natDegree (delannoy_rodrigues a b hab)
  have hC : C (a.factorial:ℝ) ≠ 0 := by simpa using (Nat.factorial_ne_zero a)
  have hX : (X+C (1:ℝ)) ≠ 0 := (monic_X_add_C (1:ℝ)).ne_zero
  rw [real_natDegree_iterate_derivative, natDegree_mul (pow_ne_zero _ X_ne_zero)
    (pow_ne_zero _ hX), natDegree_X_pow, natDegree_pow, natDegree_X_add_C,
    natDegree_mul (mul_ne_zero hC (pow_ne_zero _ hX)) (jacobiAux_ne_zero a b),
    natDegree_mul hC (pow_ne_zero _ hX), natDegree_C, natDegree_pow, natDegree_X_add_C] at h
  omega

end Fan
