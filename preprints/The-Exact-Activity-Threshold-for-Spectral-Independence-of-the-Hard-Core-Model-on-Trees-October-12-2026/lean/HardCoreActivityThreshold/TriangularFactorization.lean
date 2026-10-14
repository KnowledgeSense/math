import HardCoreActivityThreshold.GeometricMatrixBound

namespace HardCoreActivityThreshold
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem finite_geometric_left_inverse (B : Matrix V V ℝ) (N : ℕ)
    (hB : B^(N+1)=0) : (∑h : Fin (N+1),B^h.val)*(1-B)=1 := by
  rw [Fin.sum_univ_eq_sum_range,geom_sum_mul_neg,hB,sub_zero]

 theorem finite_geometric_right_inverse (B : Matrix V V ℝ) (N : ℕ)
    (hB : B^(N+1)=0) : (1-B)*(∑h : Fin (N+1),B^h.val)=1 := by
  rw [Fin.sum_univ_eq_sum_range,mul_neg_geom_sum,hB,sub_zero]

 theorem nilpotent_triangular_factorization (R B : Matrix V V ℝ) (d : V → ℝ) (N : ℕ)
    (hB : B^(N+1)=0)
    (hD : (1-B)*R*(1-B).transpose=diagonal d) :
    R=(∑h : Fin (N+1),B^h.val)*diagonal d*(∑h : Fin (N+1),B^h.val).transpose := by
  let K := ∑h : Fin (N+1),B^h.val
  have hleft : K*(1-B)=1 := finite_geometric_left_inverse B N hB
  have hright : (1-B).transpose*K.transpose=1 := by
    rw [←transpose_mul,hleft,transpose_one]
  change R=K*diagonal d*K.transpose
  rw [←hD]
  calc
    R=(K*(1-B))*R*((1-B).transpose*K.transpose) := by rw [hleft,hright,one_mul,mul_one]
    _=K*((1-B)*R*(1-B).transpose)*K.transpose := by simp only [mul_assoc]

end HardCoreActivityThreshold
