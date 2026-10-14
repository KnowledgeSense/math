import MainTheorems.DiagonalSchatten.FiniteRayMaximum

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

def groupedRayWeight (w : J → ℝ) (label : J → Fin 2) (q : Fin 2) : ℝ :=
  ∑ j, if label j = q then w j else 0

theorem groupedRayWeight_nonnegative (w : J → ℝ) (label : J → Fin 2)
    (hw : ∀ j, 0 ≤ w j) (q : Fin 2) : 0 ≤ groupedRayWeight w label q := by
  unfold groupedRayWeight
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hw j
  · exact le_rfl

theorem grouped_weighted_sum (w : J → ℝ) (label : J → Fin 2) (f : Fin 2 → ℝ) :
    (∑ q, groupedRayWeight w label q * f q) = ∑ j, w j * f (label j) := by
  unfold groupedRayWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  generalize label j = q
  fin_cases q <;> simp

theorem grouped_ray_gram (w : J → ℝ) (label : J → Fin 2)
    (d : Fin 2 → Fin 2 → ℝ) (hw : ∀ j, 0 ≤ w j) :
    let X := recoverRows (w, fun j => d (label j))
    let T := recoverRows (groupedRayWeight w label, d)
    gramFirst T = gramFirst X ∧ gramSecond T = gramSecond X ∧ gramCross T = gramCross X := by
  dsimp only
  have hg := groupedRayWeight_nonnegative w label hw
  rw [recoverRows_gramFirst hg, recoverRows_gramFirst hw,
    recoverRows_gramSecond hg, recoverRows_gramSecond hw,
    recoverRows_gramCross hg, recoverRows_gramCross hw]
  constructor
  · exact grouped_weighted_sum w label (fun q => d q 0 ^ 2)
  constructor
  · exact grouped_weighted_sum w label (fun q => d q 1 ^ 2)
  · simpa only [weightedCross, mul_assoc] using
      grouped_weighted_sum w label (fun q => d q 0 * d q 1)

theorem grouped_ray_objective (w : J → ℝ) (label : J → Fin 2)
    (d : Fin 2 → Fin 2 → ℝ) (hw : ∀ j, 0 ≤ w j)
    (h : (Fin 2 → ℝ) → ℝ)
    (hh : ∀ x t, h (t • x) = t ^ 2 * h x) :
    columnObjective h (recoverRows (groupedRayWeight w label, d)) =
      columnObjective h (recoverRows (w, fun j => d (label j))) := by
  rw [columnObjective_recover hh (groupedRayWeight_nonnegative w label hw),
    columnObjective_recover hh hw]
  exact grouped_weighted_sum w label (fun q => h (d q))

theorem grouped_ray_nonnegative (w : J → ℝ) (label : J → Fin 2)
    (d : Fin 2 → Fin 2 → ℝ)
    (hd : ∀ q i, 0 ≤ d q i) :
    ∀ i q, 0 ≤ recoverRows (groupedRayWeight w label, d) i q := by
  intro i q
  change 0 ≤ Real.sqrt (groupedRayWeight w label q) * d q i
  exact mul_nonneg (Real.sqrt_nonneg _) (hd q i)

theorem two_ray_replacement (X : Matrix (Fin 2) J ℝ)
    (w : J → ℝ) (label : J → Fin 2) (d : Fin 2 → Fin 2 → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hd : ∀ q i, 0 ≤ d q i)
    (hX : X = recoverRows (w, fun j => d (label j)))
    (h : (Fin 2 → ℝ) → ℝ) (hh : ∀ x t, h (t • x) = t ^ 2 * h x) :
    ∃ T : Matrix (Fin 2) (Fin 2) ℝ, (∀ i j, 0 ≤ T i j) ∧
      gramFirst T = gramFirst X ∧ gramSecond T = gramSecond X ∧ gramCross T = gramCross X ∧
      columnObjective h T = columnObjective h X := by
  let T := recoverRows (groupedRayWeight w label, d)
  obtain ⟨ha, hb, hc⟩ := grouped_ray_gram w label d hw
  refine ⟨T, grouped_ray_nonnegative w label d hd, ?_, ?_, ?_, ?_⟩
  · simpa only [T, hX] using ha
  · simpa only [T, hX] using hb
  · simpa only [T, hX] using hc
  · simpa only [T, hX] using grouped_ray_objective w label d hw h hh

end

end ResearchMain.DiagonalSchatten
