import Fan.KernelTuranBoundary

noncomputable section
open scoped BigOperators
namespace Fan

def reverseTruncation (A : ℕ → ℝ) (k : ℕ) : Polynomial ℝ :=
  ∑ r∈Finset.range (k+1),Polynomial.monomial r (A (k-r))

theorem reverseTruncation_coeff (A : ℕ → ℝ) (k r : ℕ) :
    (reverseTruncation A k).coeff r=zeroExtend A ((k:ℤ)-r) := by
  unfold reverseTruncation
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  by_cases hr : r≤k
  · rw [Finset.sum_eq_single r]
    · simp [zeroExtend,hr]
    · intro i _ hir
      simp [hir]
    · simp [show r<k+1 by omega]
  · have hi : ¬0≤(k:ℤ)-r := by omega
    rw [zeroExtend,ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro i hmem
    have hir : i≠r := by have := Finset.mem_range.mp hmem; omega
    simp [hir]

def kernelTuran (A B C : ℕ → ℝ) (k : ℕ) : Polynomial ℝ :=
  reverseTruncation A (k+1)^2-reverseTruncation C k*reverseTruncation B (k+2)

/-- Exact boundary telescoping, including all coefficients above the claimed degree. -/
theorem kernelTuran_coeff (A B C rho : ℕ → ℝ)
    (hA : ∀ n,A n=∑ j∈Finset.range (n+1),B j*rho (n-j))
    (hC : ∀ n,C n=∑ j∈Finset.range (n+1),A j*rho (n-j)) (k r : ℕ) :
    (kernelTuran A B C k).coeff r =
      boundaryExtended A B rho (k+1) ((k:ℤ)+1-r)-
        boundaryExtended A B rho ((k:ℤ)-r) (k+2) := by
  rw [kernelTuran,pow_two,Polynomial.coeff_sub,Polynomial.coeff_mul,Polynomial.coeff_mul,
    ← Finset.sum_sub_distrib]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (reverseTruncation A (k+1)).coeff i*(reverseTruncation A (k+1)).coeff j-
      (reverseTruncation C k).coeff i*(reverseTruncation B (k+2)).coeff j) r]
  let F : ℕ → ℝ := fun h => boundaryExtended A B rho ((k:ℤ)+1-h) ((k:ℤ)+1-r+h)
  have he (h : ℕ) (hh : h∈Finset.range (r+1)) :
      (reverseTruncation A (k+1)).coeff h*(reverseTruncation A (k+1)).coeff (r-h)-
      (reverseTruncation C k).coeff h*(reverseTruncation B (k+2)).coeff (r-h) = F h-F (h+1) := by
    have hhr : h≤r := by have := Finset.mem_range.mp hh; omega
    simp only [reverseTruncation_coeff,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
      Int.natCast_sub hhr]
    have hb := boundaryExtended_difference A B C rho hA hC ((k:ℤ)+1-h) ((k:ℤ)+1-r+h)
    dsimp [F]
    convert hb using 1 <;> congr 1 <;> ring
  rw [Finset.sum_congr rfl he]
  rw [Finset.sum_range_sub']
  dsimp [F]
  congr 1 <;> congr 1 <;> omega

end Fan
