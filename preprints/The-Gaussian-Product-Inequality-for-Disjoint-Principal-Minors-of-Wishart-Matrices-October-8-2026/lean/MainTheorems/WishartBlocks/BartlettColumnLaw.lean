import MainTheorems.WishartBlocks.BartlettColumns

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory

def belowColumnIndex {p : ℕ} (j : Fin p) (k : Fin (p - (j.val + 1))) : Fin p :=
  ⟨j.val + 1 + k.val, by omega⟩

theorem belowColumnIndex_ne {p : ℕ} (j : Fin p) (k : Fin (p - (j.val + 1))) :
    belowColumnIndex j k ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [belowColumnIndex] at hv
  omega

def columnInputIndex {p : ℕ} (j : Fin p) : Fin 1 ⊕ Fin (p - (j.val + 1)) → Fin p :=
  Sum.elim (fun _ => j) (belowColumnIndex j)

theorem columnInputIndex_injective {p : ℕ} (j : Fin p) :
    Function.Injective (columnInputIndex j) := by
  intro i k h
  cases i with
  | inl i =>
    cases k with
    | inl k => exact congrArg Sum.inl (Subsingleton.elim i k)
    | inr k => exact ((belowColumnIndex_ne j k) h.symm).elim
  | inr i =>
    cases k with
    | inl k => exact ((belowColumnIndex_ne j i) h).elim
    | inr k =>
      apply congrArg Sum.inr
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [columnInputIndex, belowColumnIndex] at hv
      omega

noncomputable def columnInput {p : ℕ} (j : Fin p) (x : Fin p → ℝ) :
    ℝ × EuclideanSpace ℝ (Fin (p - (j.val + 1))) :=
  (x j, WithLp.toLp 2 (fun k => x (belowColumnIndex j k)))

theorem bartlett_column_input_law {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (j : Fin p) :
    MeasurePreserving (columnInput j)
      (Measure.pi fun i => bartlettCoordinate α (i, j))
      ((gammaMeasure ((α - (j.val : ℝ)) / 2) (1 / 2)).prod
        (stdGaussian (EuclideanSpace ℝ (Fin (p - (j.val + 1)))))) := by
  let : ∀ ij : Fin p × Fin p, IsProbabilityMeasure (bartlettCoordinate α ij) :=
    bartlett_coordinate_probability hα
  have hs : 0 < (α - (j.val : ℝ)) / 2 := by
    have hj : (j.val : ℝ) + 1 ≤ p := by exact_mod_cast j.isLt
    linarith
  let : IsProbabilityMeasure (gammaMeasure ((α - (j.val : ℝ)) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure hs (by norm_num)
  let μ : Fin 1 ⊕ Fin (p - (j.val + 1)) → Measure ℝ :=
    Sum.elim (fun _ => gammaMeasure ((α - (j.val : ℝ)) / 2) (1 / 2))
      (fun _ => gaussianReal 0 1)
  have hμ : ∀ k, bartlettCoordinate α (columnInputIndex j k, j) = μ k := by
    intro k
    cases k with
    | inl k => simp [columnInputIndex, bartlettCoordinate, μ]
    | inr k => simp [columnInputIndex, bartlettCoordinate, belowColumnIndex_ne, μ]
  let : ∀ k, IsProbabilityMeasure (μ k) := by
    intro k
    cases k <;> dsimp [μ] <;> infer_instance
  have hselect : MeasurePreserving (fun x k => x (columnInputIndex j k))
      (Measure.pi fun i => bartlettCoordinate α (i, j)) (Measure.pi μ) := by
    refine ⟨by fun_prop, ?_⟩
    rw [finite_pi_injection _ _ (columnInputIndex_injective j)]
    simp only [hμ]
  have hsplit := measurePreserving_sumPiEquivProdPi μ
  have hdiag := measurePreserving_eval
    (fun _ : Fin 1 => gammaMeasure ((α - (j.val : ℝ)) / 2) (1 / 2)) 0
  have hgauss : MeasurePreserving (WithLp.toLp 2)
      (Measure.pi fun _ : Fin (p - (j.val + 1)) => gaussianReal 0 1)
      (stdGaussian (EuclideanSpace ℝ (Fin (p - (j.val + 1))))) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hp := (hdiag.prod hgauss).comp hsplit
  convert hp.comp hselect using 1
  funext x
  rfl

end ResearchMain.WishartBlocks
