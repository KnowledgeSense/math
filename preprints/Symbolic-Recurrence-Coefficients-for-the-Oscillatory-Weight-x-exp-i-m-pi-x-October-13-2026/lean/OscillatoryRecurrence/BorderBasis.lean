import OscillatoryRecurrence.EndpointBasis
import OscillatoryRecurrence.EndpointDeterminants

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

theorem parityBasis_nextCoeff (j : ℕ) : (parityBasis j).nextCoeff = 0 := by
  have hm : (X^2-1:ℚ[X]).Monic := monic_X_pow_sub_C 1 (by norm_num)
  rw [parityBasis, Monic.nextCoeff_mul (hm.pow _) (monic_X_pow _),
    hm.nextCoeff_pow, (monic_X : (X:ℚ[X]).Monic).nextCoeff_pow]
  have hq : (X^2-1:ℚ[X]).nextCoeff=0 := by
    rw [Polynomial.nextCoeff, show (X^2-1:ℚ[X]).natDegree=2 from natDegree_X_pow_sub_C]
    simp [Polynomial.coeff_one]
  rw [hq]
  norm_num [Polynomial.nextCoeff]

theorem parityBasis_subleading (j : ℕ) : (parityBasis (j+1)).coeff j = 0 := by
  have h := parityBasis_nextCoeff (j+1)
  simpa [Polynomial.nextCoeff, parityBasis_degree] using h

theorem borderColumn_strictMono (n : ℕ) : StrictMono (borderColumn n) := by
  intro i j hij
  unfold borderColumn
  have hi := i.isLt
  have hj := j.isLt
  have hv : i.val < j.val := hij
  split_ifs <;> omega

theorem polynomial_border_expansion (n : ℕ) (p : ℚ[X])
    (hp : p.natDegree ≤ n+1) (hc : p.coeff n=0) :
    p=∑ i : Fin (n+1), C (p.coeff (borderColumn (n+1) i))*X^(borderColumn (n+1) i) := by
  conv_lhs => rw [polynomial_fin_expansion p (by omega : p.natDegree<n+2)]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.val_last,Fin.val_castSucc,hc,map_zero,zero_mul,add_zero]
  have he (i : Fin n) : borderColumn (n+1) i.castSucc=i.val := by
    simp only [borderColumn, Fin.val_castSucc, ite_eq_right (by have := i.isLt; omega : i.val+1≠n+1)]
  rw [show borderColumn (n+1) (Fin.last n)=n+1 by simp [borderColumn]]
  simp only [he]

theorem parityBasis_border_expansion (n : ℕ) (j : Fin (n+1)) :
    parityBasis (borderColumn (n+1) j)=∑ i : Fin (n+1),
      C ((parityBasis (borderColumn (n+1) j)).coeff (borderColumn (n+1) i))*
        X^(borderColumn (n+1) i) := by
  apply polynomial_border_expansion
  · rw [parityBasis_degree]
    unfold borderColumn
    split_ifs <;> omega
  · unfold borderColumn
    split_ifs with h
    · exact parityBasis_subleading n
    · apply coeff_eq_zero_of_natDegree_lt
      rw [parityBasis_degree]
      have := j.isLt
      omega

theorem endpointBorder_change_basis (n : ℕ) :
    Matrix.det (Matrix.of (fun i j : Fin (n+1) =>
      endpointExpansion (X*parityBasis i.val*parityBasis (borderColumn (n+1) j))))=
        endpointBorder (n+1) := by
  let A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ[X] := Matrix.of
    (fun i j => C ((parityBasis j.val).coeff i.val))
  let B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ[X] := Matrix.of
    (fun i j => C ((parityBasis (borderColumn (n+1) j)).coeff (borderColumn (n+1) i)))
  let H : Matrix (Fin (n+1)) (Fin (n+1)) ℚ[X] := Matrix.of
    (fun i j => endpointExpansion (X^(i.val+borderColumn (n+1) j+1)))
  have hA : A.det=1 := by
    have h := (Polynomial.C : ℚ →+* ℚ[X]).map_det
      (Matrix.of (fun i j : Fin (n+1) => (parityBasis j.val).coeff i.val))
    rw [Matrix.det_matrixOfPolynomials _ (fun j => parityBasis_degree j.val)
      (fun j => parityBasis_monic j.val),map_one] at h
    exact h.symm
  have hB : B.det=1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_eq_one
      intro j _
      dsimp [B]
      have hc := (parityBasis_monic (borderColumn (n+1) j)).coeff_natDegree
      rw [parityBasis_degree] at hc
      rw [hc,map_one]
    · intro i j hij
      dsimp [B]
      rw [coeff_eq_zero_of_natDegree_lt, map_zero]
      rw [parityBasis_degree]
      exact borderColumn_strictMono (n+1) hij
  have he : Matrix.of (fun i j : Fin (n+1) =>
      endpointExpansion (X*parityBasis i.val*parityBasis (borderColumn (n+1) j)))=
        Aᵀ*H*B := by
    apply Matrix.ext
    intro i j
    have hi := polynomial_fin_expansion (parityBasis i.val)
      (by rw [parityBasis_degree]; exact i.isLt)
    have hj := parityBasis_border_expansion n j
    change endpointLinear (X*parityBasis i.val*parityBasis (borderColumn (n+1) j))=_
    rw [hi,hj]
    simp only [Finset.mul_sum,Finset.sum_mul,map_sum,Matrix.mul_apply,
      Matrix.transpose_apply,A,B,H,Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have hh : X*(C ((parityBasis i.val).coeff b.val)*X^b.val)*
        (C ((parityBasis (borderColumn (n+1) j)).coeff (borderColumn (n+1) a))*
          X^(borderColumn (n+1) a))=
        C ((parityBasis i.val).coeff b.val)*
        (C ((parityBasis (borderColumn (n+1) j)).coeff (borderColumn (n+1) a))*
          X^(b.val+borderColumn (n+1) a+1)) := by ring
    rw [hh,endpointLinear_C_mul,endpointLinear_C_mul]
    change C _*(C _*endpointExpansion (X^(b.val+borderColumn (n+1) a+1)))=_
    ring
  rw [he,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hA,hB,one_mul,mul_one]
  simp [endpointBorder,H]

theorem endpointBorder_basis_factor (n : ℕ) :
    endpointBorder (n+1)=
      X^((∑ i : Fin (n+1),i.val/2)+(∑ j : Fin (n+1),borderColumn (n+1) j/2)+(n+1))*
      Matrix.det (Matrix.of (fun i j : Fin (n+1) => endpointEntry i.val (borderColumn (n+1) j))) := by
  rw [← endpointBorder_change_basis]
  have he : Matrix.of (fun i j : Fin (n+1) =>
      endpointExpansion (X*parityBasis i.val*parityBasis (borderColumn (n+1) j)))=
      Matrix.of (fun i j : Fin (n+1) =>
        X^(i.val/2+1)*(X^(borderColumn (n+1) j/2)*endpointEntry i.val (borderColumn (n+1) j))) := by
    apply Matrix.ext
    intro i j
    exact endpointEntry_factor i.val (borderColumn (n+1) j)
  rw [he]
  have hc := Matrix.det_mul_column (fun i : Fin (n+1) => (X:ℚ[X])^(i.val/2+1))
    (Matrix.of (fun i j : Fin (n+1) => X^(borderColumn (n+1) j/2)*endpointEntry i.val (borderColumn (n+1) j)))
  have hr := Matrix.det_mul_row (fun j : Fin (n+1) => (X:ℚ[X])^(borderColumn (n+1) j/2))
    (Matrix.of (fun i j : Fin (n+1) => endpointEntry i.val (borderColumn (n+1) j)))
  simp only [Matrix.of_apply] at hc hr
  rw [hc,hr]
  simp only [prod_pow_eq_pow_sum,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_id]
  ring

end OscillatoryRecurrence
