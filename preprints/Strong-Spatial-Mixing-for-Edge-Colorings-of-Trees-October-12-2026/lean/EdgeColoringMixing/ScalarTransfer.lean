import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! The scalar spectral transfer, proved without any commutativity assumption. -/
namespace EdgeColoringMixing
open Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

/-- Cauchy--Schwarz also holds for a degenerate positive semidefinite form. -/
theorem semidefinite_cauchy_schwarz {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (x y : n → ℝ) :
    (x ⬝ᵥ A *ᵥ y) ^ 2 ≤ (x ⬝ᵥ A *ᵥ x) * (y ⬝ᵥ A *ᵥ y) := by
  have hy0 : 0 ≤ y ⬝ᵥ A *ᵥ y := by simpa using hA.dotProduct_mulVec_nonneg y
  by_cases hy : y ⬝ᵥ A *ᵥ y = 0
  · have hAy : A *ᵥ y = 0 := hA.dotProduct_mulVec_zero_iff.mp (by simpa using hy)
    simp [hAy]
  · have hypos : 0 < y ⬝ᵥ A *ᵥ y := lt_of_le_of_ne hy0 (Ne.symm hy)
    have h := hA.dotProduct_mulVec_nonneg
      ((y ⬝ᵥ A *ᵥ y) • x - (x ⬝ᵥ A *ᵥ y) • y)
    have hsymm : y ⬝ᵥ A *ᵥ x = x ⬝ᵥ A *ᵥ y := by
      simpa using hA.isHermitian.star_dotProduct_mulVec_comm y x
    simp only [star_trivial, mulVec_sub, mulVec_smul, sub_dotProduct,
      smul_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul, hsymm] at h
    nlinarith

/-- A factorized form of the transfer lemma: B may be rectangular and need not commute with A. -/
theorem scalar_transfer_quadratic {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (B : Matrix n m ℝ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hB : ∀ z : m → ℝ, z ⬝ᵥ (Bᵀ * A * B) *ᵥ z ≤ γ * (z ⬝ᵥ z))
    (x : n → ℝ) :
    x ⬝ᵥ (A * B * Bᵀ * A) *ᵥ x ≤ γ * (x ⬝ᵥ A *ᵥ x) := by
  let z := Bᵀ *ᵥ (A *ᵥ x)
  have hsymm : Aᵀ = A := by simpa using hA.isHermitian.eq
  have ha : 0 ≤ x ⬝ᵥ A *ᵥ x := by simpa using hA.dotProduct_mulVec_nonneg x
  have ht : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg (fun i _ => mul_self_nonneg (z i))
  have hxA : x ᵥ* A = A *ᵥ x := by simpa [hsymm] using vecMul_transpose A x
  have hid : x ⬝ᵥ A *ᵥ (B *ᵥ z) = z ⬝ᵥ z := by
    rw [dotProduct_mulVec, hxA, dotProduct_mulVec, ← mulVec_transpose]
  have heq : (B *ᵥ z) ⬝ᵥ A *ᵥ (B *ᵥ z) = z ⬝ᵥ (Bᵀ * A * B) *ᵥ z := by
    simp only [dotProduct_mulVec, vecMul_mulVec, ← vecMul_vecMul]
  have hcs := semidefinite_cauchy_schwarz hA x (B *ᵥ z)
  rw [hid, heq] at hcs
  have hbound := hB z
  have htbound : z ⬝ᵥ z ≤ γ * (x ⬝ᵥ A *ᵥ x) := by
    by_cases hz : z ⬝ᵥ z = 0
    · rw [hz]
      exact mul_nonneg hγ ha
    · have htpos : 0 < z ⬝ᵥ z := lt_of_le_of_ne ht (Ne.symm hz)
      have hm := mul_le_mul_of_nonneg_left hbound ha
      nlinarith
  have hgoal : x ⬝ᵥ (A * B * Bᵀ * A) *ᵥ x = z ⬝ᵥ z := by
    simp only [← mulVec_mulVec]
    exact hid
  rwa [hgoal]

/-- Matrix form of scalar transfer, with the Loewner order expressed by positive semidefiniteness. -/
theorem scalar_transfer_matrix [DecidableEq m] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (B : Matrix n m ℝ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hB : (γ • (1 : Matrix m m ℝ) - Bᵀ * A * B).PosSemidef) :
    (γ • A - A * B * Bᵀ * A).PosSemidef := by
  have hGram : (A * B * Bᵀ * A).PosSemidef := by
    simpa only [conjTranspose_mul, conjTranspose_eq_transpose_of_trivial, transpose_mul,
      show Aᵀ = A from by simpa using hA.isHermitian.eq, Matrix.mul_assoc] using
      Matrix.posSemidef_self_mul_conjTranspose (A * B)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((hA.smul hγ).isHermitian.sub hGram.isHermitian) ?_
  intro x
  simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  apply sub_nonneg.mpr
  apply scalar_transfer_quadratic hA B hγ
  intro z
  have h := hB.dotProduct_mulVec_nonneg z
  simpa only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_nonneg] using h

/-- Lemma 5.1 of the release: the diagonal weight need not commute with the covariance. -/
theorem scalar_transfer [DecidableEq n] {S : Matrix n n ℝ} (hS : S.PosSemidef)
    (r : n → ℝ) (hr : ∀ i, 0 ≤ r i) {γ : ℝ} (hγ : 0 ≤ γ)
    (hbound : (γ • (1 : Matrix n n ℝ) -
      Matrix.diagonal (fun i => Real.sqrt (r i)) * S *
        Matrix.diagonal (fun i => Real.sqrt (r i))).PosSemidef) :
    (γ • S - S * Matrix.diagonal r * S).PosSemidef := by
  have hroot : Matrix.diagonal (fun i => Real.sqrt (r i)) *
      Matrix.diagonal (fun i => Real.sqrt (r i)) = Matrix.diagonal r := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact Real.mul_self_sqrt (hr i)
  have h := scalar_transfer_matrix hS
    (Matrix.diagonal (fun i => Real.sqrt (r i))) hγ (by simpa using hbound)
  simpa only [Matrix.diagonal_transpose, mul_assoc, ← hroot] using h

end EdgeColoringMixing
