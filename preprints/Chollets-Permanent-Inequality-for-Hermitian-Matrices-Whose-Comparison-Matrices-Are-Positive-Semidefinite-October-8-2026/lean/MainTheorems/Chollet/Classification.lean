import MainTheorems.Chollet.BorderInduction
import MainTheorems.Chollet.Reindex
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section

namespace ResearchMain.Chollet

def successorIndex (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) :=
  borderEquivalence.symm.trans (finSuccEquiv n).symm

@[simp] theorem successorIndex_zero (n : ℕ) : successorIndex n (Sum.inl ()) = 0 := by
  simp [successorIndex, borderEquivalence]

@[simp] theorem successorIndex_succ (n : ℕ) (i : Fin n) :
    successorIndex n (Sum.inr i) = i.succ := by
  simp [successorIndex, borderEquivalence]

theorem fin_border_decomposition {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hA : A.IsHermitian) :
    A.submatrix (successorIndex n) (successorIndex n) =
      border (A 0 0).re (fun i => A i.succ 0) (A.submatrix Fin.succ Fin.succ) := by
  have him : (A 0 0).im = 0 := by
    have h := congrArg Complex.im (hA.apply 0 0)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have hdiag : A 0 0 = ((A 0 0).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using him
  ext i j
  cases i with
  | inl u =>
    cases u
    cases j with
    | inl v => cases v; simpa [border, Matrix.submatrix, Matrix.fromBlocks] using hdiag
    | inr j => simpa [border, Matrix.submatrix, Matrix.fromBlocks] using (hA.apply 0 j.succ).symm
  | inr i =>
    cases j with
    | inl u => cases u; simp [border, Matrix.submatrix, Matrix.fromBlocks]
    | inr j => simp [border, Matrix.submatrix, Matrix.fromBlocks]

theorem comparison_square_bound_fin (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ComparisonPSD A) : (squaredEntries A).permanent ≤ A.permanent.re ^ 2 := by
  induction n with
  | zero => simp [Matrix.permanent, squaredEntries]
  | succ n ih =>
    apply square_bound_by_positive_approximation A hA
    intro C hC
    let a := (C 0 0).re
    let z : Fin n → ℂ := fun i => C i.succ 0
    let B := C.submatrix Fin.succ Fin.succ
    have he : C.submatrix (successorIndex n) (successorIndex n) = border a z B :=
      fin_border_decomposition C hC.1
    have hborder : ComparisonPD (border a z B) := by
      rw [← he]
      exact hC.submatrix (successorIndex n) (successorIndex n).injective
    have ha : 0 < a := by
      have h := hC.2.diag_pos (i := (0 : Fin (n + 1)))
      simpa [comparison, a] using h
    have h := positive_border_square_bound hborder ha (fun D hD => ih D hD)
    rw [← he] at h
    change ((squaredEntries C).submatrix (successorIndex n) (successorIndex n)).permanent ≤
      (C.submatrix (successorIndex n) (successorIndex n)).permanent.re ^ 2 at h
    simpa only [permanent_reindex] using h

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem comparison_square_bound (A : Matrix I I ℂ) (hA : ComparisonPSD A) :
    (squaredEntries A).permanent ≤ A.permanent.re ^ 2 := by
  let e := (Fintype.equivFin I).symm
  have h := comparison_square_bound_fin (Fintype.card I) (A.submatrix e e)
    (hA.submatrix e e.injective)
  change ((squaredEntries A).submatrix e e).permanent ≤
    (A.submatrix e e).permanent.re ^ 2 at h
  simpa only [permanent_reindex] using h

theorem comparison_permanent_hadamard_bound (A B : Matrix I I ℂ)
    (hA : ComparisonPSD A) (hB : ComparisonPSD B) :
    (hadamard A B).permanent.re ≤ A.permanent.re * B.permanent.re :=
  pair_bound_of_square_bounds hA hB (comparison_square_bound A hA)
    (comparison_square_bound B hB)

end ResearchMain.Chollet
