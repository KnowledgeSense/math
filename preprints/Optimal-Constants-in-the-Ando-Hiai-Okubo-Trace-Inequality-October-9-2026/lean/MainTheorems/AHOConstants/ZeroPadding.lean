import MainTheorems.AHOConstants.SemidefiniteExtension
import MainTheorems.AHOConstants.PairWords
import MainTheorems.AHOConstants.FlowFactorization
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Block

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def zeroPadding (A : Matrix I I ℂ) : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks A 0 0 0

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem zeroPadding_realEntries {A : Matrix I I ℂ}
    (hreal : ∀ i j, (A i j).im = 0) :
    ∀ i j, (zeroPadding (J := J) A i j).im = 0 := by
  intro i j
  cases i <;> cases j <;> simp [zeroPadding, hreal]

omit [DecidableEq I] in
theorem zeroPadding_mul (A B : Matrix I I ℂ) :
    zeroPadding (J := J) (A * B) = zeroPadding A * zeroPadding B := by
  simp [zeroPadding, Matrix.fromBlocks_multiply]

omit [DecidableEq J] in
theorem zeroPadding_posSemidef {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (zeroPadding (J := J) A).PosSemidef := by
  let E : Matrix (I ⊕ J) I ℂ := Matrix.fromRows 1 0
  have he : E * A * Matrix.conjTranspose E = zeroPadding (J := J) A := by
    simp [E, zeroPadding, Matrix.fromRows_mul,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose]
    ext i j
    cases i <;> cases j <;> rfl
  rw [← he]
  exact hA.mul_mul_conjTranspose_same E

noncomputable def zeroPaddingHom : Matrix I I ℂ →⋆ₙₐ[ℂ] Matrix (I ⊕ J) (I ⊕ J) ℂ where
  toFun := zeroPadding
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_add' A B := by ext i j; cases i <;> cases j <;> simp [zeroPadding]
  map_mul' := zeroPadding_mul
  map_smul' r A := by ext i j; cases i <;> cases j <;> simp [zeroPadding]
  map_star' A := by
    simp only [Matrix.star_eq_conjTranspose, zeroPadding, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem zeroPadding_continuous : Continuous (zeroPadding (I := I) (J := J)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i <;> cases j <;> simp only [zeroPadding, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  all_goals fun_prop

theorem zeroPadding_spectralPower {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {r : ℝ} (hr : 0 < r) :
    spectralPower (zeroPadding (J := J) A) r = zeroPadding (spectralPower A r) := by
  let s : ℝ≥0 := ⟨r, hr.le⟩
  have hs : 0 < s := by exact_mod_cast hr
  have hP := zeroPadding_posSemidef (J := J) hA
  change (zeroPadding (J := J) A) ^ (s : ℝ) = zeroPadding (A ^ (s : ℝ))
  rw [← CFC.nnrpow_eq_rpow (a := zeroPadding (J := J) A) hs,
    ← CFC.nnrpow_eq_rpow (a := A) hs,
    CFC.nnrpow_eq_cfcₙ_real _ s hP.nonneg,
    CFC.nnrpow_eq_cfcₙ_real _ s hA.nonneg]
  exact (zeroPaddingHom (I := I) (J := J)).map_cfcₙ (R := ℝ)
    (fun x : ℝ => x ^ r) A (Real.continuous_rpow_const hr.le).continuousOn
    (Real.zero_rpow (ne_of_gt hr)) zeroPadding_continuous
    hA.isHermitian.isSelfAdjoint hP.isHermitian.isSelfAdjoint |>.symm

omit [DecidableEq I] [DecidableEq J] in
theorem zeroPadding_trace (A : Matrix I I ℂ) :
    Matrix.trace (zeroPadding (J := J) A) = Matrix.trace A := by
  simp [zeroPadding, Matrix.trace, Fintype.sum_sum_type]

theorem zeroPadding_pairProduct {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (xs : List (ℝ × ℝ)) (hne : xs ≠ [])
    (hp : ∀ pq ∈ xs, 0 < pq.1 ∧ 0 < pq.2) :
    pairProduct (zeroPadding (J := J) A) (zeroPadding B) xs =
      zeroPadding (pairProduct A B xs) := by
  revert hne hp
  induction xs with
  | nil => intro hne _; exact False.elim (hne rfl)
  | cons pq xs ih =>
    intro _ hp
    have hpair := hp pq (by simp)
    cases xs with
    | nil =>
      simp only [pairProduct, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Matrix.mul_one]
      rw [zeroPadding_spectralPower hA hpair.1, zeroPadding_spectralPower hB hpair.2,
        ← zeroPadding_mul]
    | cons pq' xs =>
      have ht := ih (by simp : pq' :: xs ≠ []) (fun t ht => hp t (by simp [ht]))
      change (spectralPower (zeroPadding A) pq.1 * spectralPower (zeroPadding B) pq.2) *
          pairProduct (zeroPadding A) (zeroPadding B) (pq' :: xs) =
        zeroPadding ((spectralPower A pq.1 * spectralPower B pq.2) * pairProduct A B (pq' :: xs))
      rw [zeroPadding_spectralPower hA hpair.1, zeroPadding_spectralPower hB hpair.2,
        ht, ← zeroPadding_mul, ← zeroPadding_mul]

theorem zeroPadding_pairTrace {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (xs : List (ℝ × ℝ)) (hne : xs ≠ [])
    (hp : ∀ pq ∈ xs, 0 < pq.1 ∧ 0 < pq.2) :
    wordTrace (zeroPadding (J := J) A) (zeroPadding B) (pairWord xs) =
      wordTrace A B (pairWord xs) := by
  unfold wordTrace
  rw [← pairProduct_eq_matrixWord, ← pairProduct_eq_matrixWord,
    zeroPadding_pairProduct hA hB xs hne hp, zeroPadding_trace]

end ResearchMain.AHOConstants
