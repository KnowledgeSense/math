import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic

noncomputable section
namespace HankelAutomaticity
open Matrix

variable {R : Type*} [CommRing R]
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

 theorem det_exchange :
    (fromBlocks (0 : Matrix b b R) (1 : Matrix b b R) (1 : Matrix b b R) 0).det = (-1 : R)^Fintype.card b := by
  have he : fromBlocks (0 : Matrix b b R) (1 : Matrix b b R) (1 : Matrix b b R) 0 =
      fromBlocks (1 : Matrix b b R) 0 (1 : Matrix b b R) 1 *
      fromBlocks (1 : Matrix b b R) (-1 : Matrix b b R) 0 1 *
      fromBlocks (1 : Matrix b b R) 0 (1 : Matrix b b R) 1 *
      fromBlocks (1 : Matrix b b R) 0 0 (-1 : Matrix b b R) := by
    simp [fromBlocks_multiply]
  rw [he]
  simp [det_mul, det_fromBlocks_zero₂₁, det_neg]

/-- Eliminate an arbitrary paired block without assuming any pivot is nonzero.
The cross blocks touching the zero corner may be completely arbitrary. -/
 theorem det_paired_corner (C : Matrix a a R) (E : Matrix a b R)
    (F : Matrix b a R) (G U V : Matrix b b R) :
    (fromBlocks C (fromCols E 0) (fromRows F 0) (fromBlocks G U V 0)).det =
      (-1 : R)^Fintype.card b * C.det * U.det * V.det := by
  let M := fromBlocks C (fromCols E 0) (fromRows F 0) (fromBlocks G U V 0)
  let S := fromBlocks (1 : Matrix a a R) 0 0
    (fromBlocks (0 : Matrix b b R) (1 : Matrix b b R) (1 : Matrix b b R) 0)
  have hS : S.det=(-1 : R)^Fintype.card b := by
    dsimp [S]
    rw [det_fromBlocks_zero₁₂, det_one, one_mul, det_exchange]
  have he : (M*S).submatrix (Equiv.sumAssoc a b b)
      (Equiv.sumAssoc a b b) =
      fromBlocks (fromBlocks C 0 F U) (fromRows E G) 0 V := by
    ext i j
    rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
      simp [M, S, fromBlocks_multiply, Matrix.mul_apply, Fintype.sum_sum_type,
        fromCols, fromRows, Equiv.sumAssoc, Sum.elim, Matrix.one_apply]
  have hd := congrArg Matrix.det he
  rw [det_submatrix_equiv_self, det_mul, hS,
    det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at hd
  have hs : ((-1 : R)^Fintype.card b)^2=1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    simp
  change M.det * (-1 : R)^Fintype.card b=C.det*U.det*V.det at hd
  change M.det = _
  linear_combination (-1 : R)^Fintype.card b*hd-M.det*hs

/-- Simultaneous elementary block shears preserve the determinant. -/
 theorem det_block_shear (A : Matrix a a R) (B : Matrix a b R)
    (C : Matrix b a R) (D : Matrix b b R) (T : Matrix b a R) :
    (fromBlocks A (B+A*T.transpose) (C+T*A)
      (D+T*B+C*T.transpose+T*A*T.transpose)).det =
      (fromBlocks A B C D).det := by
  let S := fromBlocks (1 : Matrix a a R) 0 T (1 : Matrix b b R)
  have hs : S.det=1 := by simp [S]
  have he : fromBlocks A (B+A*T.transpose) (C+T*A)
      (D+T*B+C*T.transpose+T*A*T.transpose) =
      S * fromBlocks A B C D * S.transpose := by
    simp [S, fromBlocks_multiply, fromBlocks_transpose, Matrix.add_mul,
      add_comm, add_assoc]
  rw [he, det_mul, det_mul, det_transpose, hs, one_mul, mul_one]

end HankelAutomaticity

namespace HankelAutomaticity
open Matrix
variable {R : Type*} [CommRing R]
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
 theorem det_upper_block_shear (A : Matrix a a R) (B : Matrix a b R)
    (C : Matrix b a R) (D : Matrix b b R) (T : Matrix a b R) :
    (fromBlocks (A+T*C+B*T.transpose+T*D*T.transpose) (B+T*D)
      (C+D*T.transpose) D).det=(fromBlocks A B C D).det := by
  let S := fromBlocks (1 : Matrix a a R) T 0 (1 : Matrix b b R)
  have hs : S.det=1 := by simp [S]
  have he : fromBlocks (A+T*C+B*T.transpose+T*D*T.transpose) (B+T*D)
      (C+D*T.transpose) D = S*fromBlocks A B C D*S.transpose := by
    simp [S, fromBlocks_multiply, fromBlocks_transpose, Matrix.add_mul, add_assoc]
  rw [he, det_mul, det_mul, det_transpose, hs, one_mul, mul_one]
end HankelAutomaticity
