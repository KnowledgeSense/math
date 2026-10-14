import MainTheorems.WishartBlocks.BartlettColumnLaw
import MainTheorems.WishartBlocks.ColumnPrecision
import MainTheorems.WishartBlocks.SupportedQuadratic

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators InnerProductSpace

theorem columnInputIndex_range {p : ℕ} (j i : Fin p) :
    i ∈ Set.range (columnInputIndex j) ↔ j ≤ i := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | inl k => exact le_rfl
    | inr k => change j.val ≤ j.val + 1 + k.val; omega
  · intro hi
    by_cases hij : i = j
    · exact ⟨Sum.inl 0, hij.symm⟩
    · have hji : j.val < i.val := by
        have hv : j.val ≤ i.val := hi
        have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        omega
      refine ⟨Sum.inr ⟨i.val - j.val - 1, by omega⟩, ?_⟩
      apply Fin.ext
      dsimp [columnInputIndex, belowColumnIndex]
      omega

theorem bartlettColumn_selected {p : ℕ} (j : Fin p) (x : Fin p → ℝ) :
    bartlettColumn j x ∘ columnInputIndex j =
      Sum.elim (fun _ : Fin 1 => Real.sqrt (x j))
        (fun k => x (belowColumnIndex j k)) := by
  funext k
  cases k with
  | inl k => simp [bartlettColumn, columnInputIndex]
  | inr k =>
      have hlt : j < belowColumnIndex j k := by
        change j.val < j.val + 1 + k.val
        omega
      simp [bartlettColumn, columnInputIndex, belowColumnIndex_ne, hlt]

theorem bartlettColumn_support {p : ℕ} (j i : Fin p) (x : Fin p → ℝ)
    (hi : i ∉ Set.range (columnInputIndex j)) : bartlettColumn j x i = 0 := by
  have hji : ¬j ≤ i := fun h => hi ((columnInputIndex_range j i).mpr h)
  have hij : i ≠ j := fun h => hji (h ▸ le_rfl)
  have hlt : ¬j < i := fun h => hji h.le
  simp [bartlettColumn, hij, hlt]

noncomputable def columnCross {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    EuclideanSpace ℝ (Fin (p - (j.val + 1))) :=
  WithLp.toLp 2 (fun k => T (belowColumnIndex j k) j)

def trailingColumnMatrix {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    Matrix (Fin (p - (j.val + 1))) (Fin (p - (j.val + 1))) ℝ :=
  T.submatrix (belowColumnIndex j) (belowColumnIndex j)

theorem column_submatrix_precision {p : ℕ} {T : Matrix (Fin p) (Fin p) ℝ}
    (hT : T.IsHermitian) (j : Fin p) :
    T.submatrix (columnInputIndex j) (columnInputIndex j) =
      columnPrecision (T j j) (columnCross T j) (trailingColumnMatrix T j) := by
  ext i k
  cases i with
  | inl i =>
      cases k with
      | inl k => rfl
      | inr k =>
          change T j (belowColumnIndex j k) = T (belowColumnIndex j k) j
          simpa only [star_trivial] using hT.apply (belowColumnIndex j k) j
  | inr i =>
      cases k <;> rfl

theorem bartlettColumn_quadratic_kernel {p : ℕ} {T : Matrix (Fin p) (Fin p) ℝ}
    (hT : T.IsHermitian) (j : Fin p) (x : Fin p → ℝ) :
    Real.exp (-(bartlettColumn j x ⬝ᵥ (T *ᵥ bartlettColumn j x))) =
      gammaColumnKernel (T j j) (columnCross T j) (trailingColumnMatrix T j)
        (columnInput j x) := by
  rw [quadratic_submatrix_support (columnInputIndex j) (columnInputIndex_injective j)
    T (bartlettColumn j x) (fun i => bartlettColumn_support j i x)]
  rw [bartlettColumn_selected, column_submatrix_precision hT]
  have h := columnPrecision_quadratic (T j j) (Real.sqrt (x j))
    (columnCross T j) (WithLp.toLp 2 (fun k => x (belowColumnIndex j k)))
    (trailingColumnMatrix T j)
  exact congrArg (fun y : ℝ => Real.exp (-y)) h

theorem bartlett_column_laplace {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) {T : Matrix (Fin p) (Fin p) ℝ}
    (hT : T.PosSemidef) (j : Fin p) :
    ∫ x : Fin p → ℝ,
        Real.exp (-(bartlettColumn j x ⬝ᵥ (T *ᵥ bartlettColumn j x)))
        ∂(Measure.pi fun i => bartlettCoordinate α (i, j)) =
      (1 + (2 : ℝ) • T.submatrix (columnInputIndex j) (columnInputIndex j)).det ^
          (-(α - (j.val : ℝ)) / 2) *
        (1 + (2 : ℝ) • trailingColumnMatrix T j).det ^
          ((α - (j.val : ℝ)) / 2 - (1 / 2 : ℝ)) := by
  have hp := bartlett_column_input_law hα j
  have hs : 0 < (α - (j.val : ℝ)) / 2 := by
    have hj : (j.val : ℝ) + 1 ≤ p := by exact_mod_cast j.isLt
    linarith
  have hP : (columnPrecision (T j j) (columnCross T j)
      (trailingColumnMatrix T j)).PosSemidef := by
    rw [← column_submatrix_precision hT.1]
    exact hT.submatrix (columnInputIndex j)
  simp_rw [bartlettColumn_quadratic_kernel hT.1]
  rw [← integral_map hp.measurable.aemeasurable (by
    unfold gammaColumnKernel columnQuadratic
    fun_prop), hp.map_eq,
    gamma_column_laplace_determinants hP hs, ← column_submatrix_precision hT.1]
  simp only [neg_div]

end ResearchMain.WishartBlocks
