import Fan.WeightedTransferCenter

noncomputable section
open scoped BigOperators
namespace Fan

def weightedKernel (z : ℝ) (n k : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i : Fin (n+1),kernelEntry z n k i*x i

theorem weightedKernel_pos (z : ℝ) (hz : 0 ≤ z) (n k : ℕ) (hk : k ≤ n)
    (x : ℕ → ℝ) (hx : ∀ i,0 ≤ x i) (hx0 : 0<x 0) : 0<weightedKernel z n k x := by
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (kernelEntry_nonneg z hz n k i) (hx i)
  · refine ⟨0,Finset.mem_univ _,?_⟩
    have he : kernelEntry z n k 0=delannoy z k (n-k) := by simp [kernelEntry,hk]
    change 0<kernelEntry z n k 0*x 0
    rw [he]
    exact mul_pos (delannoy_pos hz _ _) hx0

theorem weightedKernel_symm (z : ℝ) (n k : ℕ) (hk : k ≤ n) (x : ℕ → ℝ) :
    weightedKernel z n (n-k) x=weightedKernel z n k x := by
  simp only [weightedKernel,kernelEntry_symm z n k _ hk]

theorem weightedKernel_increasing (z : ℝ) (hz : 0<z) (n k : ℕ) (hk : 2*k+2 ≤ n)
    (x : ℕ → ℝ) (hx : ∀ i,0 ≤ x i) (hx0 : 0<x 0) :
    weightedKernel z n k x<weightedKernel z n (k+1) x := by
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_right (kernelEntry_towards_center z hz n k i hk) (hx i)
  · refine ⟨0,Finset.mem_univ _,?_⟩
    exact mul_lt_mul_of_pos_right (kernelEntry_center_zero_strict z hz n k hk) hx0

theorem weightedKernel_lower_strict (z : ℝ) (hz : 0<z) (n k : ℕ)
    (hk : 1 ≤ k) (hmid : 2*k+2 ≤ n) (x : ℕ → ℝ)
    (hx : ∀ i,0 ≤ x i) (hx0 : 0<x 0)
    (hp : ∀ R r,2*r+2 ≤ R → x r*x (R-r) ≤ x (r+1)*x (R-r-1)) :
    weightedKernel z n (k-1) x*weightedKernel z n (k+1) x<weightedKernel z n k x^2 := by
  let M : Fin (n+1) → Fin (n+1) → ℝ := fun i j =>
    kernelEntry z n k i*kernelEntry z n k j-
      kernelEntry z n (k-1) i*kernelEntry z n (k+1) j
  have hM (R h : ℕ) : 0 ≤ quadraticTail M R h := by
    rw [quadraticTail_polynomials]
    exact kernelTail_turan_nonneg z hz n k h R hk hmid
  have hM0 : 0<M 0 0 := by
    have h := kernelPolynomial_turan_positive z hz n k 0 hk hmid (by omega)
    simp only [pow_two,Polynomial.coeff_sub,Polynomial.mul_coeff_zero,
      kernelPolynomial_coeff z n k 0 (by omega),kernelPolynomial_coeff z n (k-1) 0 (by omega),
      kernelPolynomial_coeff z n (k+1) 0 (by omega)] at h
    exact h
  have h := weighted_quadratic_pos M x hx hx0 hp hM hM0
  have he : (∑ i,∑ j,M i j*x i*x j) =
      weightedKernel z n k x^2-weightedKernel z n (k-1) x*weightedKernel z n (k+1) x := by
    simp only [weightedKernel,pow_two,Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [M]
    ring
  rw [he] at h
  exact sub_pos.mp h

theorem weightedKernel_half_strict (z : ℝ) (hz : 0<z) (n k : ℕ)
    (hk : 1 ≤ k) (hmid : 2*k ≤ n) (x : ℕ → ℝ)
    (hx : ∀ i,0 ≤ x i) (hx0 : 0<x 0)
    (hp : ∀ R r,2*r+2 ≤ R → x r*x (R-r) ≤ x (r+1)*x (R-r-1)) :
    weightedKernel z n (k-1) x*weightedKernel z n (k+1) x<weightedKernel z n k x^2 := by
  by_cases hm : 2*k+2 ≤ n
  · exact weightedKernel_lower_strict z hz n k hk hm x hx hx0 hp
  · have hn : n=2*k ∨ n=2*k+1 := by omega
    have hi := weightedKernel_increasing z hz n (k-1) (by omega) x hx hx0
    rw [show k-1+1=k by omega] at hi
    have hpos := weightedKernel_pos z hz.le n k (by omega) x hx hx0
    have hprev := weightedKernel_pos z hz.le n (k-1) (by omega) x hx hx0
    rcases hn with hn | hn
    · have he : weightedKernel z n (k+1) x=weightedKernel z n (k-1) x := by
        rw [← weightedKernel_symm z n (k+1) (by omega) x]
        congr 1
        omega
      rw [he]
      nlinarith
    · have he : weightedKernel z n (k+1) x=weightedKernel z n k x := by
        rw [← weightedKernel_symm z n (k+1) (by omega) x]
        congr 1
        omega
      rw [he]
      nlinarith

/-- Strict log-concavity transfer for every internal fixed-total index, with exact finite weights. -/
theorem weightedKernel_strict_log_concave (z : ℝ) (hz : 0<z) (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k<n) (x : ℕ → ℝ)
    (hx : ∀ i,0 ≤ x i) (hx0 : 0<x 0)
    (hp : ∀ R r,2*r+2 ≤ R → x r*x (R-r) ≤ x (r+1)*x (R-r-1)) :
    weightedKernel z n (k-1) x*weightedKernel z n (k+1) x<weightedKernel z n k x^2 := by
  by_cases hm : 2*k ≤ n
  · exact weightedKernel_half_strict z hz n k hk hm x hx hx0 hp
  · have h := weightedKernel_half_strict z hz n (n-k) (by omega) (by omega) x hx hx0 hp
    have h1 : n-k-1=n-(k+1) := by omega
    have h2 : n-k+1=n-(k-1) := by omega
    rw [h1,h2,weightedKernel_symm z n (k+1) (by omega) x,
      weightedKernel_symm z n (k-1) (by omega) x,weightedKernel_symm z n k (by omega) x] at h
    simpa only [mul_comm] using h

end Fan
