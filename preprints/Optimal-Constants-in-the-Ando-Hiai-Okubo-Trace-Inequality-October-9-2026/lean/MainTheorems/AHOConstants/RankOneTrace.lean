import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

def rankOne (u v : I → R) : Matrix I I R := fun i j => u i * v j

def vectorPairing (u v : I → R) : R := ∑ i, u i * v i

def lastVector (u : I → R) : List (I → R) → I → R
  | [] => u
  | v :: w => lastVector v w

def pairingProduct (u : I → R) : List (I → R) → R
  | [] => 1
  | v :: w => vectorPairing u v * pairingProduct v w

omit [DecidableEq I] in
theorem rankOne_mul (u v w z : I → R) :
    rankOne u v * rankOne w z = vectorPairing v w • rankOne u z := by
  ext i j
  simp only [Matrix.mul_apply, rankOne, vectorPairing, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  ring

omit [DecidableEq I] in
theorem rankOne_trace (u v : I → R) :
    Matrix.trace (rankOne u v) = vectorPairing u v := rfl

theorem rankOne_product (u : I → R) (w : List (I → R)) :
    ((u :: w).map (fun v => rankOne v v)).prod =
      pairingProduct u w • rankOne u (lastVector u w) := by
  induction w generalizing u with
  | nil => simp [pairingProduct, lastVector]
  | cons v w ih =>
    rw [List.map_cons, List.prod_cons, ih v, Matrix.mul_smul, rankOne_mul]
    simp only [pairingProduct, lastVector, smul_smul]
    rw [mul_comm (pairingProduct v w) (vectorPairing u v)]

theorem rankOne_product_trace (u : I → R) (w : List (I → R)) :
    Matrix.trace ((u :: w).map (fun v => rankOne v v)).prod =
      pairingProduct u w * vectorPairing u (lastVector u w) := by
  rw [rankOne_product, Matrix.trace_smul, rankOne_trace, smul_eq_mul]

end ResearchMain.AHOConstants
