import CokernelPolynomiality

open CokernelPolynomiality Polynomial

-- Every admissible rank, including the smallest rank for each positive defect.
example (i n : ℕ) (h : i ≤ n+1) :
    (r n (n+1-i) : ℚ) = (defectPolynomial i).eval (n : ℚ) :=
  (defectPolynomial_eval i n h).symm

example (i : ℕ) :
    (r i 0 : ℚ) = (defectPolynomial (i+1)).eval (i : ℚ) := by
  simpa using (defectPolynomial_eval (i+1) i (by omega)).symm

example (n : ℕ) :
    (r n (n+1) : ℚ) = (defectPolynomial 0).eval (n : ℚ) := by
  simpa using (defectPolynomial_eval 0 n (by omega)).symm

example : (defectPolynomial 3).natDegree = 6 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (defectPolynomial_degree_le 3)
  rw [defectPolynomial_top_coeff]
  norm_num [Nat.factorial]

example : (defectPolynomial 3).coeff 6 = 1/6 := by
  convert defectPolynomial_top_coeff 3 using 1; norm_num [Nat.factorial]

example (n i m : ℕ) (h : n+1 = i+m) :
    r n m = ∑ q : Fin (2*i+1), templateCount i q * m.choose q :=
  r_binomial_formula n i m h

example (i : ℕ) : templateCount i (2*i) = (2*i).descFactorial i :=
  top_template_count i


-- The count here is defined from actual categorical subcategories.
example (n k : ℕ) : categoryCount n k = r n k := categoryCount_eq_r n k

example (i n : ℕ) (hn : i ≤ n+1) :
    (categoryCount n (n+1-i) : ℚ)=(defectPolynomial i).eval (n : ℚ) := by
  rw [categoryCount_eq_r]
  exact (defectPolynomial_eval i n hn).symm

example (n : ℕ) :
    (categoryCount n 0 : ℚ)=(defectPolynomial (n+1)).eval (n : ℚ) := by
  simpa using (show (categoryCount n (n+1-(n+1)) : ℚ)=
    (defectPolynomial (n+1)).eval (n : ℚ) from by
      rw [categoryCount_eq_r]
      exact (defectPolynomial_eval (n+1) n le_rfl).symm)

example : ∀ i : ℕ, ∃ P : Polynomial ℚ,
    (∀ n : ℕ, i ≤ n+1 → (categoryCount n (n+1-i) : ℚ)=P.eval (n : ℚ)) ∧
    P.natDegree=2*i ∧ P.coeff (2*i)=(i.factorial : ℚ)⁻¹ :=
  categoricalFixedDefectPolynomiality
