import MainTheorems.WishartBlocks.SpectralLaw.Weyl.Coordinates
import Mathlib.LinearAlgebra.UnitaryGroup

namespace ResearchMain.WishartBlocks.Weyl

noncomputable def signValue (s : Bool) : ℝ := if s then 1 else -1

noncomputable def signMatrix {n : ℕ} (s : Fin n → Bool) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (signValue ∘ s)

theorem signMatrix_mem {n : ℕ} (s : Fin n → Bool) :
    signMatrix s ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, signMatrix, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    cases hs : s i <;> simp [signValue, hs]
  · simp [hij]

noncomputable def signOrthogonal {n : ℕ} (s : Fin n → Bool) :
    Matrix.orthogonalGroup (Fin n) ℝ := ⟨signMatrix s, signMatrix_mem s⟩

theorem signOrthogonal_injective (n : ℕ) :
    Function.Injective (signOrthogonal (n := n)) := by
  intro s t h
  funext i
  have hi := congrArg (fun U : Matrix.orthogonalGroup (Fin n) ℝ => U.val i i) h
  have hi' : signValue (s i) = signValue (t i) := by
    simpa only [signOrthogonal, signMatrix, Matrix.diagonal_apply_eq,
      Function.comp_apply] using hi
  cases hs : s i <;> cases ht : t i <;> simp_all [signValue]
  all_goals norm_num at hi'

theorem signMatrix_stabilizes_diagonal {n : ℕ}
    (s : Fin n → Bool) (lam : Fin n → ℝ) :
    signMatrix s * Matrix.diagonal lam * (signMatrix s).transpose = Matrix.diagonal lam := by
  rw [signMatrix, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    cases hs : s i <;> simp [signValue, hs]
  · simp [hij]

theorem orthogonal_stabilizer_commutes {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ)
    (hU : U.val * Matrix.diagonal lam * U.val.transpose = Matrix.diagonal lam) :
    U.val * Matrix.diagonal lam = Matrix.diagonal lam * U.val := by
  have hunit := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.property
  have h := congrArg (fun W : Matrix (Fin n) (Fin n) ℝ => W * U.val) hU
  simpa only [Matrix.mul_assoc, hunit, Matrix.mul_one] using h

theorem orthogonal_stabilizer_diagonal {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ)
    (hlam : Function.Injective lam)
    (hU : U.val * Matrix.diagonal lam * U.val.transpose = Matrix.diagonal lam) :
    U.val = Matrix.diagonal (fun i => U.val i i) := by
  have hcomm := orthogonal_stabilizer_commutes U lam hU
  have hoff (i j : Fin n) (hij : i ≠ j) : U.val i j = 0 := by
    have h := congrArg (fun W : Matrix (Fin n) (Fin n) ℝ => W i j) hcomm
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hlamij : lam j ≠ lam i := fun h => hij (hlam h).symm
    have hz : U.val i j * (lam j - lam i) = 0 := by nlinarith
    exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hlamij)
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
  · simp only [Matrix.diagonal_apply, hij, ite_false, hoff i j hij]

theorem orthogonal_stabilizer_is_sign {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ)
    (hlam : Function.Injective lam)
    (hU : U.val * Matrix.diagonal lam * U.val.transpose = Matrix.diagonal lam) :
    ∃ s : Fin n → Bool, U = signOrthogonal s := by
  classical
  have hdiag := orthogonal_stabilizer_diagonal U lam hlam hU
  have hpm (i : Fin n) : U.val i i = 1 ∨ U.val i i = -1 := by
    have hunit := (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp U.property
    have h := congrArg (fun W : Matrix (Fin n) (Fin n) ℝ => W i i) hunit
    rw [hdiag, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal] at h
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply, ite_true] at h
    exact mul_self_eq_one_iff.mp h
  let s : Fin n → Bool := fun i => decide (U.val i i = 1)
  have hs (i : Fin n) : signValue (s i) = U.val i i := by
    by_cases hi : U.val i i = 1
    · simp [s, signValue, hi]
    · have hn := (hpm i).resolve_left hi
      simp [s, signValue, hn]
      norm_num
  refine ⟨s, Subtype.ext ?_⟩
  change U.val = signMatrix s
  rw [hdiag]
  unfold signMatrix
  congr 1
  funext i
  exact (hs i).symm

def DiagonalStabilizer {n : ℕ} (lam : Fin n → ℝ) :=
  {U : Matrix.orthogonalGroup (Fin n) ℝ //
    U.val * Matrix.diagonal lam * U.val.transpose = Matrix.diagonal lam}

noncomputable def signStabilizerEquiv {n : ℕ}
    (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    (Fin n → Bool) ≃ DiagonalStabilizer lam :=
  Equiv.ofBijective
    (fun s => ⟨signOrthogonal s, signMatrix_stabilizes_diagonal s lam⟩)
    ⟨by
      intro s t h
      exact signOrthogonal_injective n (congrArg Subtype.val h), by
      intro U
      obtain ⟨s, hs⟩ := orthogonal_stabilizer_is_sign U.val lam hlam U.property
      exact ⟨s, Subtype.ext hs.symm⟩⟩

theorem diagonalStabilizer_card {n : ℕ} (lam : Fin n → ℝ)
    (hlam : Function.Injective lam) :
    Nat.card (DiagonalStabilizer lam) = 2 ^ n := by
  rw [Nat.card_congr (signStabilizerEquiv lam hlam).symm]
  simp

end ResearchMain.WishartBlocks.Weyl
