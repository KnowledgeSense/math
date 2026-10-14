import MainTheorems.WishartBlocks.SpectralLaw.OrthogonalInvariance
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix TopologicalSpace

theorem isCompact_orthogonalGroup (n : ℕ) :
    IsCompact (Matrix.orthogonalGroup (Fin n) ℝ :
      Set (Matrix (Fin n) (Fin n) ℝ)) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).matrix.of_isClosed_subset
    (isClosed_unitary (R := Matrix (Fin n) (Fin n) ℝ))
  intro U hU i j
  have h := entry_norm_bound_of_unitary hU i j
  simpa only [Set.mem_Icc, Real.norm_eq_abs, abs_le] using h

instance orthogonalGroup_compactSpace (n : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ) :=
  isCompact_iff_compactSpace.mp (isCompact_orthogonalGroup n)

noncomputable def orthogonalHaar (n : ℕ) :
    Measure (Matrix.orthogonalGroup (Fin n) ℝ) :=
  Measure.haarMeasure ⊤

instance orthogonalHaar_probability (n : ℕ) :
    IsProbabilityMeasure (orthogonalHaar n) where
  measure_univ := by
    change Measure.haarMeasure
      (⊤ : PositiveCompacts (Matrix.orthogonalGroup (Fin n) ℝ)) Set.univ = 1
    simpa only [PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self (K₀ :=
        (⊤ : PositiveCompacts (Matrix.orthogonalGroup (Fin n) ℝ))))

instance orthogonalHaar_isHaarMeasure (n : ℕ) :
    Measure.IsHaarMeasure (orthogonalHaar n) := by
  unfold orthogonalHaar
  infer_instance

instance orthogonalHaar_rightInvariant (n : ℕ) :
    Measure.IsMulRightInvariant (orthogonalHaar n) where
  map_mul_right_eq_self U :=
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure
      ((orthogonalHaar n).map (· * U)) (orthogonalHaar n)

noncomputable def orthogonalAverage {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∫ U, G (matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ) W)
    ∂orthogonalHaar n

theorem orthogonalAverage_congruence {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    orthogonalAverage G (matrixCongruence (U : Matrix (Fin n) (Fin n) ℝ) W) =
      orthogonalAverage G W := by
  unfold orthogonalAverage
  simp_rw [← matrixCongruence_orthogonal_mul]
  exact integral_mul_right_eq_self (μ := orthogonalHaar n)
    (fun V : Matrix.orthogonalGroup (Fin n) ℝ =>
      G (matrixCongruence (V : Matrix (Fin n) (Fin n) ℝ) W)) U

end ResearchMain.WishartBlocks
