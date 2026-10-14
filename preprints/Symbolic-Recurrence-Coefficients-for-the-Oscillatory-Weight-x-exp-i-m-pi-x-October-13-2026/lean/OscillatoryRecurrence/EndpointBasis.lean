import OscillatoryRecurrence.EndpointExpansion
import OscillatoryRecurrence.Nonvanishing

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

 def endpointLinear : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun := endpointExpansion
  map_add' := endpointExpansion_add
  map_smul' := by
    intro a p
    simp only [smul_eq_C_mul,RingHom.id_apply]
    exact endpointExpansion_C_mul a p

 theorem polynomial_fin_expansion {n : ℕ} (p : ℚ[X]) (hp : p.natDegree<n) :
    p=∑ i : Fin n, C (p.coeff i.val)*X^i.val := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => C (p.coeff i)*X^i) n]
  simpa only [C_mul_X_pow_eq_monomial] using p.as_sum_range' n hp

 theorem endpointLinear_C_mul (a : ℚ) (p : ℚ[X]) :
    endpointLinear (C a*p)=C a*endpointLinear p := endpointExpansion_C_mul a p

 theorem endpointGram_change_basis {n : ℕ} (p : Fin n → ℚ[X])
    (hp : ∀i,(p i).natDegree=i.val) (hm : ∀i,(p i).Monic) :
    Matrix.det (Matrix.of (fun i j => endpointExpansion (X*p i*p j)))=
      Matrix.det (Matrix.of (fun i j : Fin n => endpointExpansion (X^(i.val+j.val+1)))) := by
  let Cmat : Matrix (Fin n) (Fin n) ℚ[X] := Matrix.of (fun i j => C ((p j).coeff i.val))
  let H : Matrix (Fin n) (Fin n) ℚ[X] := Matrix.of
    (fun i j => endpointExpansion (X^(i.val+j.val+1)))
  have hC : Cmat.det=1 := by
    have he := (Polynomial.C : ℚ →+* ℚ[X]).map_det (Matrix.of (fun i j : Fin n => (p j).coeff i.val))
    rw [Matrix.det_matrixOfPolynomials p hp hm,map_one] at he
    exact he.symm
  have he : Matrix.of (fun i j => endpointExpansion (X*p i*p j))=Cmat.transpose*H*Cmat := by
    apply Matrix.ext
    intro i j
    have hi := polynomial_fin_expansion (p i) (by rw [hp]; exact i.isLt)
    have hj := polynomial_fin_expansion (p j) (by rw [hp]; exact j.isLt)
    change endpointLinear (X*p i*p j)=_
    rw [hi,hj]
    simp only [Finset.mul_sum,Finset.sum_mul,map_sum,Matrix.mul_apply,
      Matrix.transpose_apply,Cmat,H,Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    have hpoly : (X*(C ((p i).coeff b.val)*X^b.val))*(C ((p j).coeff a.val)*X^a.val)=
        C ((p i).coeff b.val)* (C ((p j).coeff a.val)*X^(b.val+a.val+1)) := by ring
    rw [hpoly,endpointLinear_C_mul,endpointLinear_C_mul]
    change C ((p i).coeff b.val)*(C ((p j).coeff a.val)*endpointExpansion (X^(b.val+a.val+1)))=_
    ring
  rw [he,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hC,one_mul,mul_one]

/-- A monic basis adapted to the two endpoints. -/
def parityBasis (j : ℕ) : ℚ[X] := (X^2-1)^(j/2)*X^(j%2)

 theorem parityBasis_monic (j : ℕ) : (parityBasis j).Monic := by
  apply Monic.mul
  · exact (monic_X_pow_sub_C (1:ℚ) (by norm_num : 2≠0)).pow _
  · exact monic_X_pow _

 theorem parityBasis_degree (j : ℕ) : (parityBasis j).natDegree=j := by
  have hm : (X^2-1:ℚ[X]).Monic := monic_X_pow_sub_C 1 (by norm_num)
  rw [parityBasis,(hm.pow _).natDegree_mul (monic_X_pow _),natDegree_pow,
    show (X^2-1:ℚ[X]).natDegree=2 from natDegree_X_pow_sub_C,natDegree_X_pow]
  omega

 theorem parityBasis_product (i j : ℕ) :
    X*parityBasis i*parityBasis j=(X^2-1)^(i/2+j/2)*X^(i%2+j%2+1) := by
  unfold parityBasis
  rw [pow_add,pow_add,pow_succ]
  ring

 def endpointEntry (i j : ℕ) : ℚ[X] :=
  factorialTransform (i/2+j/2) (endpointTail 1 (i/2+j/2) (i%2+j%2+1))-
    factorialTransform (i/2+j/2) (endpointTail (-1) (i/2+j/2) (i%2+j%2+1))

 theorem endpointEntry_factor (i j : ℕ) :
    endpointExpansion (X*parityBasis i*parityBasis j)=
      X^(i/2+1)*(X^(j/2)*endpointEntry i j) := by
  rw [parityBasis_product,endpointExpansion_factor]
  unfold endpointEntry
  ring

 theorem endpointEntry_eval_zero (i j : ℕ) :
    (endpointEntry i j).eval 0=((i/2+j/2).factorial:ℚ)*
      ((-2)^(i/2+j/2)-2^(i/2+j/2)*(-1)^(i%2+j%2+1)) := by
  rw [← coeff_zero_eq_eval_zero]
  simp only [endpointEntry,coeff_sub,factorialTransform_coeff,
    endpointTail_coeff_zero,zero_add,one_pow,mul_one,mul_neg,neg_neg]
  ring

 theorem endpointBasis_determinant (n : ℕ) :
    Matrix.det (Matrix.of (fun i j : Fin n => endpointExpansion (X^(i.val+j.val+1))))=
      X^((∑ i : Fin n,i.val/2)+(∑ i : Fin n,i.val/2)+n)*
        Matrix.det (Matrix.of (fun i j : Fin n => endpointEntry i.val j.val)) := by
  rw [← endpointGram_change_basis (fun i : Fin n => parityBasis i.val)
    (fun i => parityBasis_degree i.val) (fun i => parityBasis_monic i.val)]
  have he : Matrix.of (fun i j : Fin n => endpointExpansion (X*parityBasis i.val*parityBasis j.val))=
      Matrix.of (fun i j : Fin n => X^(i.val/2+1)*(X^(j.val/2)*endpointEntry i.val j.val)) := by
    apply Matrix.ext
    intro i j
    exact endpointEntry_factor i.val j.val
  rw [he]
  have hc := Matrix.det_mul_column (fun i : Fin n => (X:ℚ[X])^(i.val/2+1))
    (Matrix.of (fun i j : Fin n => X^(j.val/2)*endpointEntry i.val j.val))
  have hr := Matrix.det_mul_row (fun j : Fin n => (X:ℚ[X])^(j.val/2))
    (Matrix.of (fun i j : Fin n => endpointEntry i.val j.val))
  simp only [Matrix.of_apply] at hc hr
  rw [hc,hr]
  simp only [prod_pow_eq_pow_sum,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_id]
  ring

end OscillatoryRecurrence
