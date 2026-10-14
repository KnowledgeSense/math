import HankelAutomaticity.DyadicMoments
import HankelAutomaticity.BlockElimination

noncomputable section
namespace HankelAutomaticity
open Matrix

 def prefixSelect {m d : ℕ} (h : d≤m) : Matrix (Fin d) (Fin m) ℚ :=
  fun i j => if j=Fin.castLE h i then 1 else 0

 theorem prefixSelect_mul {m d : ℕ} {a : Type*} (h : d≤m)
    (A : Matrix (Fin m) a ℚ) (i : Fin d) (j : a) :
    (prefixSelect h*A) i j=A (Fin.castLE h i) j := by
  simp [Matrix.mul_apply, prefixSelect]

 theorem mul_prefixSelect_transpose {m d : ℕ} {a : Type*} (h : d≤m)
    (A : Matrix a (Fin m) ℚ) (i : a) (j : Fin d) :
    (A*(prefixSelect h).transpose) i j=A i (Fin.castLE h j) := by
  simp [Matrix.mul_apply, prefixSelect, Matrix.transpose_apply]

 def firstReduced (L d : ℕ) (x z : ℚ) :
    Matrix (Fin (2^L) ⊕ Fin d) (Fin (2^L) ⊕ Fin d) ℚ :=
  fromBlocks
    (Matrix.of fun i j => (digitSum (i.val+j.val) : ℚ)+z)
    (Matrix.of fun i j => 1+(x-2)*(if 2^L ≤ i.val+j.val then 1 else 0))
    (Matrix.of fun i j => 1+(x-2)*(if 2^L ≤ i.val+j.val then 1 else 0))
    (Matrix.of fun i j => (x-2)-2*(x-2)*(if 2^L ≤ i.val+j.val then 1 else 0))

 theorem first_reduction (L d : ℕ) (hd : d≤2^L) (x z : ℚ) :
    (firstReduced L d x z).det =
      (hankelMatrix L (2^L+d) x+(Matrix.of fun (_ : Fin (2^L+d)) (_ : Fin (2^L+d)) => z)).det := by
  let A : Matrix (Fin (2^L)) (Fin (2^L)) ℚ :=
    Matrix.of fun i j => weightedMoment L x (i.val+j.val)+z
  let B : Matrix (Fin (2^L)) (Fin d) ℚ :=
    Matrix.of fun i j => weightedMoment L x (i.val+j.val+2^L)+z
  let C : Matrix (Fin d) (Fin (2^L)) ℚ :=
    Matrix.of fun i j => weightedMoment L x (i.val+j.val+2^L)+z
  let D : Matrix (Fin d) (Fin d) ℚ :=
    Matrix.of fun i j => weightedMoment L x (i.val+j.val+2*2^L)+z
  let E := prefixSelect hd
  have ho : (hankelMatrix L (2^L+d) x+(Matrix.of fun (_ : Fin (2^L+d)) (_ : Fin (2^L+d)) => z)).submatrix
      finSumFinEquiv finSumFinEquiv=fromBlocks A B C D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, A, B, C, D, hankelMatrix, Matrix.submatrix, finSumFinEquiv,
        add_comm, add_left_comm, add_assoc, two_mul]
  have he : firstReduced L d x z=fromBlocks A (B+A*(-E).transpose)
      (C+(-E)*A) (D+(-E)*B+C*(-E).transpose+(-E)*A*(-E).transpose) := by
    unfold firstReduced
    apply Matrix.fromBlocks_inj.mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext i j
      have hij : i.val+j.val<2^(L+1) := by
        have hi := i.isLt
        have hj := j.isLt
        rw [pow_succ]
        omega
      simp [A, weightedMoment_below x hij]
    · ext i j
      have hij : i.val+j.val<2*2^L := by have := i.isLt; have := j.isLt; omega
      have hw := weightedMoment_first_difference x hij
      simp only [Matrix.add_apply, transpose_neg, Matrix.mul_neg, Matrix.neg_apply]
      rw [show (A*E.transpose) i j=A i (Fin.castLE hd j) from
        mul_prefixSelect_transpose hd A i j]
      dsimp [A, B]
      linear_combination -hw
    · ext i j
      have hij : i.val+j.val<2*2^L := by have := i.isLt; have := j.isLt; omega
      have hw := weightedMoment_first_difference x hij
      simp only [Matrix.add_apply, Matrix.neg_mul, Matrix.neg_apply]
      rw [show (E*A) i j=A (Fin.castLE hd i) j from prefixSelect_mul hd A i j]
      dsimp [A, C]
      linear_combination -hw
    · ext i j
      have hij : i.val+j.val<2*2^L := by have := i.isLt; have := j.isLt; omega
      have hw := weightedMoment_second_difference x hij
      simp only [Matrix.add_apply, transpose_neg, Matrix.mul_neg, Matrix.neg_mul,
        neg_neg, Matrix.neg_apply]
      rw [show (E*B) i j=B (Fin.castLE hd i) j from prefixSelect_mul hd B i j,
        show (C*E.transpose) i j=C i (Fin.castLE hd j) from
          mul_prefixSelect_transpose hd C i j,
        show (E*A*E.transpose) i j=(E*A) i (Fin.castLE hd j) from
          mul_prefixSelect_transpose hd (E*A) i j,
        show (E*A) i (Fin.castLE hd j)=A (Fin.castLE hd i) (Fin.castLE hd j) from
          prefixSelect_mul hd A i (Fin.castLE hd j)]
      dsimp [A, B, C, D]
      linear_combination -hw
  rw [he, det_block_shear, ← ho, det_submatrix_equiv_self]

end HankelAutomaticity
