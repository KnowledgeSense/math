import Fan.DelannoyRodrigues

noncomputable section
open Polynomial
open scoped BigOperators
namespace Fan

private theorem mobius_monomial (a k : ℕ) (hk : k ≤ a) (z : ℝ) (hz : z ≠ 1) :
    (1-z)^a * ((z/(1-z))^k * (z/(1-z)+1)^(a-k)) = z^k := by
  have hd : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hlin : z/(1-z)+1 = 1/(1-z) := by field_simp; ring
  rw [hlin, div_pow, div_pow, one_pow, div_mul_div_comm, mul_one,
    ← pow_add, Nat.add_sub_of_le hk]
  field_simp

/-- The exact fractional-linear transformation from the Rodrigues quotient. -/
theorem delannoy_mobius (a b : ℕ) (hab : a ≤ b) (z : ℝ) (hz : z ≠ 1) :
    (1-z)^a * (jacobiAux a b).eval (z/(1-z)) = delannoy z a b := by
  simp only [jacobiAux, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_add,
    Finset.mul_sum]
  unfold delannoy
  rw [min_eq_left hab]
  apply Finset.sum_congr rfl
  intro k hk
  have hka : k ≤ a := by simpa using Finset.mem_range.mp hk
  have hm := mobius_monomial a k hka z hz
  calc
    _ = ((a.choose k:ℝ) * b.choose k) *
        ((1-z)^a * ((z/(1-z))^k * (z/(1-z)+1)^(a-k))) := by ring
    _ = _ := by rw [hm]

/-- A split linear-factor expression for the elementary binomial kernel. -/
def delannoyFactors (a b : ℕ) : Polynomial ℝ :=
  C (jacobiAux a b).leadingCoeff *
    ((jacobiAux a b).roots.map (fun x => C (1+x)*X-C x)).prod

private theorem scaled_root_product (m : Multiset ℝ) (z : ℝ) (hz : z ≠ 1) :
    (1-z)^m.card * (m.map (fun x => z/(1-z)-x)).prod =
      (m.map (fun x => (1+x)*z-x)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons x m ih =>
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ]
    have he : (1-z)*(z/(1-z)-x) = (1+x)*z-x := by
      field_simp [sub_ne_zero.mpr (Ne.symm hz)]
      ring
    calc
      _ = ((1-z)*(z/(1-z)-x)) * ((1-z)^m.card * (m.map (fun x => z/(1-z)-x)).prod) := by ring
      _ = _ := by rw [he,ih]

theorem delannoy_factorization (a b : ℕ) (hab : a ≤ b) :
    delannoyPolynomial a b = delannoyFactors a b := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Set.Infinite {z : ℝ | z ≠ 1} := by
    convert (Set.infinite_univ : Set.Infinite (Set.univ : Set ℝ)).sdiff (Set.finite_singleton 1) using 1
    ext z
    simp
  apply hi.mono
  intro z hz
  change (delannoyPolynomial a b).eval z = (delannoyFactors a b).eval z
  rw [delannoyPolynomial_eval, ← delannoy_mobius a b hab z hz]
  rw [(jacobiAux_splits a b hab).eval_eq_prod_roots]
  have hc : (jacobiAux a b).roots.card = a :=
    (jacobiAux_splits a b hab).natDegree_eq_card_roots.symm.trans (jacobiAux_natDegree a b hab)
  have hm := scaled_root_product (jacobiAux a b).roots z hz
  rw [hc] at hm
  simp only [delannoyFactors, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map,
    Function.comp_def, eval_sub, eval_X]
  calc
    _ = (jacobiAux a b).leadingCoeff *
      ((1-z)^a * ((jacobiAux a b).roots.map (fun x => z/(1-z)-x)).prod) := by ring
    _ = _ := by rw [hm]

theorem delannoyPolynomial_splits (a b : ℕ) (hab : a ≤ b) :
    (delannoyPolynomial a b).Splits := by
  rw [delannoy_factorization a b hab]
  unfold delannoyFactors
  apply Splits.C_mul
  apply Splits.multisetProd
  intro q hq
  obtain ⟨x,_,rfl⟩ := Multiset.mem_map.mp hq
  apply Splits.of_natDegree_le_one
  compute_degree

/-- All real roots of the elementary binomial kernel are negative. -/
theorem delannoyPolynomial_roots_neg (a b : ℕ) (hab : a ≤ b) :
    ∀ z ∈ (delannoyPolynomial a b).roots, z < 0 := by
  intro z hz
  have he : (delannoyPolynomial a b).eval z = 0 :=
    (mem_roots (delannoyPolynomial_ne_zero a b)).mp hz
  rw [delannoy_factorization a b hab] at he
  simp only [delannoyFactors, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map,
    Function.comp_def, eval_sub, eval_X] at he
  have hlc : (jacobiAux a b).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (jacobiAux_ne_zero a b)
  have hp := (mul_eq_zero.mp he).resolve_left hlc
  have ht := Multiset.prod_eq_zero_iff.mp hp
  obtain ⟨x,hx,hzero⟩ := Multiset.mem_map.mp ht
  have hbds := jacobiAux_roots_interval a b hab x hx
  have hc : 0 < 1+x := by linarith
  have heq : (1+x)*z=x := by linarith
  by_contra hh
  have hz0 : 0 ≤ z := le_of_not_gt hh
  have hm := mul_nonneg hc.le hz0
  linarith

end Fan
