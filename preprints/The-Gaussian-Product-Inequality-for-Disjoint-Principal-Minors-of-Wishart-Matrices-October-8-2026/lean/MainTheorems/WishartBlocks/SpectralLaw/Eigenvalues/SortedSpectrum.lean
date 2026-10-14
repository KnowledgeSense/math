import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

abbrev SymmetricMatrix (n : ℕ) :=
  {W : Matrix (Fin n) (Fin n) ℝ // W.IsHermitian}

noncomputable def spectralPermutation (n : ℕ) : Equiv.Perm (Fin n) :=
  (Fin.revPerm.trans (finCongr (Fintype.card_fin n).symm)).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))))

noncomputable def ascendingSpectrum {n : ℕ} (W : SymmetricMatrix n) : Fin n → ℝ :=
  fun i => W.property.eigenvalues (spectralPermutation n i)

theorem ascendingSpectrum_eq_eigenvalues₀ {n : ℕ} (W : SymmetricMatrix n) (i : Fin n) :
    ascendingSpectrum W i =
      W.property.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i.rev) := by
  simp only [ascendingSpectrum, Matrix.IsHermitian.eigenvalues,
    spectralPermutation, Equiv.trans_apply, Equiv.symm_apply_apply, Fin.revPerm_apply,
    finCongr_apply]

theorem ascendingSpectrum_monotone {n : ℕ} (W : SymmetricMatrix n) :
    Monotone (ascendingSpectrum W) := by
  intro i j hij
  rw [ascendingSpectrum_eq_eigenvalues₀, ascendingSpectrum_eq_eigenvalues₀]
  apply W.property.eigenvalues₀_antitone
  exact (Fin.cast_le_cast _).mpr (Fin.rev_le_rev.mpr hij)

theorem ascendingSpectrum_charpoly {n : ℕ} (W : SymmetricMatrix n) :
    W.val.charpoly = (Matrix.diagonal (ascendingSpectrum W)).charpoly := by
  rw [W.property.charpoly_eq, Matrix.charpoly_diagonal]
  symm
  exact Equiv.prod_comp (spectralPermutation n)
    (fun i => Polynomial.X - Polynomial.C (W.property.eigenvalues i))

theorem roots_diagonal_charpoly {n : ℕ} (x : Fin n → ℝ) :
    (Matrix.diagonal x).charpoly.roots = (List.ofFn x : Multiset ℝ) := by
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp [Fin.univ_val_map]
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

theorem monotone_diagonal_charpoly_injective {n : ℕ} {x y : Fin n → ℝ}
    (hx : Monotone x) (hy : Monotone y)
    (h : (Matrix.diagonal x).charpoly = (Matrix.diagonal y).charpoly) : x = y := by
  have hr := congrArg Polynomial.roots h
  rw [roots_diagonal_charpoly, roots_diagonal_charpoly] at hr
  have hs := congrArg (fun s : Multiset ℝ => s.sort (· ≤ ·)) hr
  simp only [Multiset.coe_sort] at hs
  have hsx : (List.ofFn x).mergeSort (fun a b => decide (a ≤ b)) = List.ofFn x :=
    List.mergeSort_of_pairwise (by simpa only [decide_eq_true_eq] using hx.sortedLE_ofFn.pairwise)
  have hsy : (List.ofFn y).mergeSort (fun a b => decide (a ≤ b)) = List.ofFn y :=
    List.mergeSort_of_pairwise (by simpa only [decide_eq_true_eq] using hy.sortedLE_ofFn.pairwise)
  rw [hsx, hsy] at hs
  exact List.ofFn_inj.mp hs

theorem ascendingSpectrum_eq_iff {n : ℕ} (W : SymmetricMatrix n) (x : Fin n → ℝ) :
    ascendingSpectrum W = x ↔
      Monotone x ∧ W.val.charpoly = (Matrix.diagonal x).charpoly := by
  constructor
  · rintro rfl
    exact ⟨ascendingSpectrum_monotone W, ascendingSpectrum_charpoly W⟩
  · rintro ⟨hx, h⟩
    exact monotone_diagonal_charpoly_injective (ascendingSpectrum_monotone W) hx
      ((ascendingSpectrum_charpoly W).symm.trans h)

theorem ascendingSpectrum_norm_le {n : ℕ} (W : SymmetricMatrix n) (i : Fin n) :
    ‖ascendingSpectrum W i‖ ≤ ‖W.val‖ * ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ :=
  spectrum.norm_le_norm_mul_of_mem
    (W.property.eigenvalues_mem_spectrum_real (spectralPermutation n i))

theorem ascendingSpectrum_trace {n : ℕ} (W : SymmetricMatrix n) :
    W.val.trace = ∑ i, ascendingSpectrum W i := by
  rw [W.property.trace_eq_sum_eigenvalues]
  exact (Equiv.sum_comp (spectralPermutation n) W.property.eigenvalues).symm

theorem ascendingSpectrum_det {n : ℕ} (W : SymmetricMatrix n) :
    W.val.det = ∏ i, ascendingSpectrum W i := by
  rw [W.property.det_eq_prod_eigenvalues]
  exact (Equiv.prod_comp (spectralPermutation n) W.property.eigenvalues).symm

theorem ascendingSpectrum_nonneg {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosSemidef) (i : Fin n) : 0 ≤ ascendingSpectrum ⟨W, hW.isHermitian⟩ i :=
  hW.eigenvalues_nonneg (spectralPermutation n i)

theorem ascendingSpectrum_pos {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W.PosDef) (i : Fin n) : 0 < ascendingSpectrum ⟨W, hW.isHermitian⟩ i :=
  hW.eigenvalues_pos (spectralPermutation n i)

end ResearchMain.WishartBlocks
