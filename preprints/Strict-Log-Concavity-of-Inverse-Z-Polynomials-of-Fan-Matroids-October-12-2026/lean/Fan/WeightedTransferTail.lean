import Fan.WeightedTransferAbel

noncomputable section
open scoped BigOperators
namespace Fan

def kernelEntry (z : ℝ) (n k r : ℕ) : ℝ :=
  if r ≤ k ∧ k+r ≤ n then delannoy z (k-r) (n-k-r) else 0

theorem kernelPolynomial_coeff (z : ℝ) (n k r : ℕ) (hk : k ≤ n) :
    (kernelPolynomial z n k).coeff r=kernelEntry z n k r := by
  unfold kernelPolynomial kernelEntry
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  by_cases hr : r ≤ k ∧ k+r ≤ n
  · rw [ite_eq_left hr,Finset.sum_eq_single r]
    · simp
    · intro i _ hir; simp [hir]
    · have hm : r<min k (n-k)+1 := by omega
      simp [hm]
  · rw [ite_eq_right hr]
    apply Finset.sum_eq_zero
    intro i hi
    have hir : i≠r := by have := Finset.mem_range.mp hi; omega
    simp [hir]

def tailPolynomial {N : ℕ} (f : Fin (N+1) → ℝ) (h : ℕ) : Polynomial ℝ :=
  ∑ i,Polynomial.monomial i.val (if h ≤ i.val then f i else 0)

theorem tailPolynomial_coeff {N : ℕ} (f : Fin (N+1) → ℝ) (h r : ℕ) :
    (tailPolynomial f h).coeff r=if hr : r ≤ N then (if h ≤ r then f ⟨r,by omega⟩ else 0) else 0 := by
  simp only [tailPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  by_cases hr : r ≤ N
  · rw [dite_eq_left hr,Finset.sum_eq_single (⟨r,by omega⟩ : Fin (N+1))]
    · simp
    · intro i _ hi
      have hir : i.val≠r := fun h => hi (Fin.ext h)
      simp [hir]
    · simp
  · rw [dite_eq_right hr]
    apply Finset.sum_eq_zero
    intro i _
    have hir : i.val≠r := by have := i.isLt; omega
    simp [hir]

theorem tailPolynomial_product_coeff {N : ℕ} (f g : Fin (N+1) → ℝ) (h R : ℕ) :
    (tailPolynomial f h*tailPolynomial g h).coeff R=
      ∑ i,∑ j,if i.val+j.val=R ∧ h ≤ i.val ∧ h ≤ j.val then f i*g j else 0 := by
  simp only [tailPolynomial,Finset.sum_mul,Finset.mul_sum,Polynomial.finsetSum_coeff,
    Polynomial.monomial_mul_monomial,Polynomial.coeff_monomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp_all

theorem quadraticTail_polynomials {N : ℕ} (f g l : Fin (N+1) → ℝ) (h R : ℕ) :
    quadraticTail (fun i j => f i*f j-g i*l j) R h=
      (tailPolynomial f h^2-tailPolynomial g h*tailPolynomial l h).coeff R := by
  rw [pow_two,Polynomial.coeff_sub,tailPolynomial_product_coeff,tailPolynomial_product_coeff]
  simp only [quadraticTail,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

def kernelTail (z : ℝ) (n k h : ℕ) : Polynomial ℝ :=
  tailPolynomial (fun i : Fin (n+1) => kernelEntry z n k i) h

theorem kernelTail_coeff (z : ℝ) (n k h r : ℕ) (hk : k ≤ n) :
    (kernelTail z n k h).coeff r=if h ≤ r then kernelEntry z n k r else 0 := by
  rw [kernelTail,tailPolynomial_coeff]
  by_cases hr : r ≤ n
  · simp only [hr,dite_true]
  · have he : kernelEntry z n k r=0 := by
      unfold kernelEntry
      exact ite_eq_right (by omega)
    simp only [hr,dite_false,he,ite_self]

theorem kernelTail_above (z : ℝ) (n k h : ℕ) (hk : k ≤ n) (hh : k<h) :
    kernelTail z n k h=0 := by
  ext r
  rw [kernelTail_coeff z n k h r hk,Polynomial.coeff_zero]
  by_cases hr : h ≤ r
  · rw [ite_eq_left hr,kernelEntry,ite_eq_right (by omega)]
  · rw [ite_eq_right hr]

theorem kernelTail_shift (z : ℝ) (n k h : ℕ) (hh : h ≤ k) (hk : k+h ≤ n) :
    kernelTail z n k h=Polynomial.X^h*kernelPolynomial z (n-2*h) (k-h) := by
  ext r
  rw [kernelTail_coeff z n k h r (by omega),Polynomial.coeff_X_pow_mul']
  by_cases hr : h ≤ r
  · rw [ite_eq_left hr,ite_eq_left hr,kernelPolynomial_coeff z (n-2*h) (k-h) (r-h) (by omega)]
    unfold kernelEntry
    have he : r ≤ k ∧ k+r ≤ n ↔ r-h ≤ k-h ∧ k-h+(r-h) ≤ n-2*h := by omega
    simp only [he]
    split_ifs with hs
    · have hs' := he.mpr hs
      have h1 : k-r=k-h-(r-h) := by omega
      have h2 : n-k-r=n-2*h-(k-h)-(r-h) := by omega
      rw [h1,h2]
    · rfl
  · rw [ite_eq_right hr,ite_eq_right hr]

theorem kernelTail_diagonal (z : ℝ) (n k : ℕ) (hk : 2*k ≤ n) :
    kernelTail z n k k=Polynomial.X^k := by
  rw [kernelTail_shift z n k k le_rfl (by omega)]
  simp [kernelPolynomial]

theorem kernelTail_turan_nonneg (z : ℝ) (hz : 0<z) (n k h R : ℕ)
    (hk : 1 ≤ k) (hmid : 2*k+2 ≤ n) :
    0 ≤ (kernelTail z n k h^2-kernelTail z n (k-1) h*kernelTail z n (k+1) h).coeff R := by
  by_cases hh : h<k
  · rw [kernelTail_shift z n k h (by omega) (by omega),
      kernelTail_shift z n (k-1) h (by omega) (by omega),
      kernelTail_shift z n (k+1) h (by omega) (by omega)]
    have he : (Polynomial.X^h*kernelPolynomial z (n-2*h) (k-h))^2-
        (Polynomial.X^h*kernelPolynomial z (n-2*h) (k-1-h))*
          (Polynomial.X^h*kernelPolynomial z (n-2*h) (k+1-h)) =
        Polynomial.X^(2*h)*(kernelPolynomial z (n-2*h) (k-h)^2-
          kernelPolynomial z (n-2*h) (k-h-1)*kernelPolynomial z (n-2*h) (k-h+1)) := by
      rw [show k-1-h=k-h-1 by omega,show k+1-h=k-h+1 by omega]
      ring
    rw [he,Polynomial.coeff_X_pow_mul']
    split_ifs
    · exact kernelPolynomial_turan_nonneg z hz (n-2*h) (k-h) _ (by omega) (by omega)
    · exact le_rfl
  · by_cases he : h=k
    · subst h
      rw [kernelTail_diagonal z n k (by omega),kernelTail_above z n (k-1) k (by omega) (by omega)]
      simp only [zero_mul,sub_zero,← pow_mul,Polynomial.coeff_X_pow]
      split_ifs <;> norm_num
    · rw [kernelTail_above z n k h (by omega) (by omega),
        kernelTail_above z n (k-1) h (by omega) (by omega)]
      simp

end Fan
