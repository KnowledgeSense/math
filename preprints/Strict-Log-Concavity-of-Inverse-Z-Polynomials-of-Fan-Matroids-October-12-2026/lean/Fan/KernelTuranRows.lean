import Fan.KernelTuran

noncomputable section
open scoped BigOperators
namespace Fan

/-- The fixed-total antidiagonal kernel, with its actual finite common-shift sum. -/
def kernelPolynomial (z : ℝ) (n k : ℕ) : Polynomial ℝ :=
  ∑ r∈Finset.range (min k (n-k)+1),Polynomial.monomial r (delannoy z (k-r) (n-k-r))

theorem kernelPolynomial_symm (z : ℝ) (n k : ℕ) (hk : k≤n) :
    kernelPolynomial z n (n-k)=kernelPolynomial z n k := by
  unfold kernelPolynomial
  rw [Nat.sub_sub_self hk,min_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [delannoy_symm]

theorem kernelPolynomial_reverse (z : ℝ) (k e : ℕ) :
    kernelPolynomial z (2*k+e) k=reverseTruncation (fun m => delannoy z m (m+e)) k := by
  unfold kernelPolynomial reverseTruncation
  have hn : 2*k+e-k=k+e := by omega
  rw [hn,min_eq_left (by omega)]
  apply Finset.sum_congr rfl
  intro r hr
  have h : r≤k := by have := Finset.mem_range.mp hr; omega
  rw [show k+e-r=k-r+e by omega]

theorem kernelPolynomial_turan_identification (z : ℝ) (e k : ℕ) :
    kernelPolynomial z (2*(k+1)+e+2) (k+1)^2-
      kernelPolynomial z (2*(k+1)+e+2) k*kernelPolynomial z (2*(k+1)+e+2) (k+2) =
      delannoyTuran z e k := by
  have h0 : 2*(k+1)+e+2=2*(k+1)+(e+2) := by omega
  have h1 : 2*(k+1)+e+2=2*k+(e+4) := by omega
  have h2 : 2*(k+1)+e+2=2*(k+2)+e := by omega
  rw [h0,kernelPolynomial_reverse]
  rw [← h0,h1,kernelPolynomial_reverse]
  rw [← h1,h2,kernelPolynomial_reverse]
  simp only [delannoyTuran,kernelTuran,Nat.add_assoc]

theorem kernelPolynomial_turan_positive (z : ℝ) (hz : 0<z) (n k r : ℕ)
    (hk : 1≤k) (hmid : 2*k+2≤n) (hr : r≤k) :
    0<(kernelPolynomial z n k^2-kernelPolynomial z n (k-1)*kernelPolynomial z n (k+1)).coeff r := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  let e := n-(2*(j+1)+2)
  have hn : n=2*(j+1)+e+2 := by dsimp [e]; omega
  rw [hn]
  rw [show j.succ-1=j by omega,show j.succ+1=j+2 from rfl]
  rw [kernelPolynomial_turan_identification]
  exact delannoyTuran_coeff_positive z hz e j r hr

theorem kernelPolynomial_turan_above (z : ℝ) (n k r : ℕ)
    (hk : 1≤k) (hmid : 2*k+2≤n) (hr : k<r) :
    (kernelPolynomial z n k^2-kernelPolynomial z n (k-1)*kernelPolynomial z n (k+1)).coeff r=0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  let e := n-(2*(j+1)+2)
  have hn : n=2*(j+1)+e+2 := by dsimp [e]; omega
  rw [hn]
  rw [show j.succ-1=j by omega,show j.succ+1=j+2 from rfl]
  rw [kernelPolynomial_turan_identification]
  exact delannoyTuran_coeff_above z e j r hr

theorem kernelPolynomial_turan_nonneg (z : ℝ) (hz : 0<z) (n k r : ℕ)
    (hk : 1≤k) (hmid : 2*k+2≤n) :
    0≤(kernelPolynomial z n k^2-kernelPolynomial z n (k-1)*kernelPolynomial z n (k+1)).coeff r := by
  by_cases hr : r≤k
  · exact (kernelPolynomial_turan_positive z hz n k r hk hmid hr).le
  · rw [kernelPolynomial_turan_above z n k r hk hmid (by omega)]

end Fan
