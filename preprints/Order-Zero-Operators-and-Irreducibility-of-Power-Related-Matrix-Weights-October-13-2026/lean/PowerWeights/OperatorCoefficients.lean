import PowerWeights.MatrixIntegration

namespace PowerWeights

open Polynomial

@[simp] theorem coefficient_add {N : ℕ} (P Q : PolynomialMatrix N) (n : ℕ) :
    coefficient (P+Q) n=coefficient P n+coefficient Q n := by
  ext i j
  simp [coefficient]

@[simp] theorem coefficient_sum {N : ℕ} {α : Type*} (t : Finset α)
    (P : α → PolynomialMatrix N) (n : ℕ) :
    coefficient (∑ j ∈ t, P j) n=∑ j ∈ t, coefficient (P j) n := by
  ext i j
  simp [coefficient,Matrix.sum_apply]

 theorem coefficient_power_constant {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (j n : ℕ) :
    coefficient ((X : ℂ[X])^j • constant F) n=if n=j then F else 0 := by
  apply Matrix.ext
  intro i k
  change ((X : ℂ[X])^j * Polynomial.C (F i k)).coeff n = _
  rw [mul_comm,Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n=j <;> simp [hn]

 theorem coefficient_power_one (N j n : ℕ) :
    coefficient ((X : ℂ[X])^j • (1 : PolynomialMatrix N)) n=
      if n=j then 1 else 0 := by
  rw [← constant_one N]
  exact coefficient_power_constant _ _ _

 theorem monic_top_coefficient {N : ℕ} {I : Set ℝ} {w : ℝ → ℝ}
    {P : PolynomialMatrix N} (Q : MonicOrthogonalSequence I w P) (n : ℕ) :
    coefficient (Q.Q n) n=1 := by
  rw [Q.monic,coefficient_add,coefficient_sum,coefficient_power_one]
  have hz : (∑ j ∈ Finset.range n, coefficient ((X : ℂ[X])^j • constant (Q.lower n j)) n)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [coefficient_power_constant,ite_eq_right]
    have := Finset.mem_range.mp hj
    omega
  rw [hz]
  simp

 theorem monic_lower_coefficient {N : ℕ} {I : Set ℝ} {w : ℝ → ℝ}
    {P : PolynomialMatrix N} (Q : MonicOrthogonalSequence I w P) (n j : ℕ)
    (hj : j<n) : coefficient (Q.Q n) j=Q.lower n j := by
  rw [Q.monic,coefficient_add,coefficient_sum,coefficient_power_one,
    ite_eq_right (Nat.ne_of_lt hj),zero_add]
  rw [Finset.sum_eq_single j,coefficient_power_constant,ite_eq_left rfl]
  · intro t _ ht
    rw [coefficient_power_constant,ite_eq_right (Ne.symm ht)]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hj))

 theorem monic_zero {N : ℕ} {I : Set ℝ} {w : ℝ → ℝ}
    {P : PolynomialMatrix N} (Q : MonicOrthogonalSequence I w P) : Q.Q 0=1 := by
  simp [Q.monic]

 theorem coefficient_constant_left {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ)
    (P : PolynomialMatrix N) (n : ℕ) :
    coefficient (constant F*P) n=F*coefficient P n := by
  ext i j
  simp [coefficient,constant,Matrix.mul_apply,Polynomial.coeff_C_mul]

 theorem coefficient_constant_right {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ)
    (P : PolynomialMatrix N) (n : ℕ) :
    coefficient (P*constant F) n=coefficient P n*F := by
  ext i j
  simp [coefficient,constant,Matrix.mul_apply,Polynomial.coeff_mul_C]

 theorem eigenoperator_constant_and_commuting {N : ℕ} {I : Set ℝ} {w : ℝ → ℝ}
    {P : PolynomialMatrix N} (Q : MonicOrthogonalSequence I w P)
    (B : PolynomialMatrix N) (hB : IsOrderZeroEigenoperator Q B) :
    ∃ C₀ : Matrix (Fin N) (Fin N) ℂ, B=constant C₀ ∧
      ∀ n j, j<n → C₀*Q.lower n j=Q.lower n j*C₀ := by
  obtain ⟨C₀,hC⟩ := hB 0
  rw [monic_zero,one_mul,mul_one] at hC
  refine ⟨C₀,hC,?_⟩
  intro n j hj
  obtain ⟨Λ,hΛ⟩ := hB n
  rw [hC] at hΛ
  have htop := congrArg (fun P : PolynomialMatrix N => coefficient P n) hΛ
  rw [coefficient_constant_right,coefficient_constant_left,monic_top_coefficient,
    one_mul,mul_one] at htop
  rw [← htop] at hΛ
  have hc := congrArg (fun P : PolynomialMatrix N => coefficient P j) hΛ
  rw [coefficient_constant_right,coefficient_constant_left,monic_lower_coefficient Q n j hj] at hc
  exact hc.symm

end PowerWeights
