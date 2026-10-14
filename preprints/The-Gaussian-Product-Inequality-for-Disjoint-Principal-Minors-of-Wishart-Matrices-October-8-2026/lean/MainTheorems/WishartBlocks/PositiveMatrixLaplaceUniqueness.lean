import MainTheorems.WishartBlocks.WishartLaplace
import MainTheorems.WishartBlocks.KernelMeasureUniqueness
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Topology.MetricSpace.Polish

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix BoundedContinuousFunction
open scoped BigOperators MatrixOrder InnerProductSpace Matrix.Norms.Elementwise

def positiveMatrixMonoid (p : ℕ) : AddSubmonoid (Matrix (Fin p) (Fin p) ℝ) where
  carrier := {A | A.PosSemidef}
  zero_mem' := Matrix.PosSemidef.zero
  add_mem' := fun hA hB => hA.add hB

instance positiveMatrix_polish (p : ℕ) : PolishSpace (positiveMatrixMonoid p) := by
  let : PolishSpace (Matrix (Fin p) (Fin p) ℝ) :=
    inferInstanceAs (PolishSpace (Fin p → Fin p → ℝ))
  change PolishSpace {A : Matrix (Fin p) (Fin p) ℝ // A.PosSemidef}
  exact Matrix.posSemidef_is_closed.polishSpace

theorem trace_positive_product {p : ℕ} {A B : Matrix (Fin p) (Fin p) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ Matrix.trace (A * B) := by
  have hR : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hRt : (CFC.sqrt A).conjTranspose = CFC.sqrt A := hR.1.eq
  have h := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [hRt, Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at h
  exact h

theorem hermitian_eq_of_positive_trace {p : ℕ}
    {A B : Matrix (Fin p) (Fin p) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ T : Matrix (Fin p) (Fin p) ℝ, T.PosSemidef →
      Matrix.trace (T * A) = Matrix.trace (T * B)) : A = B := by
  have hq (x : EuclideanSpace ℝ (Fin p)) :
      ⟪x, A.toEuclideanLin x⟫_ℝ = ⟪x, B.toEuclideanLin x⟫_ℝ := by
    have hv : (Matrix.vecMulVec (fun i => x i) (fun i => x i)).PosSemidef := by
      simpa only [star_trivial] using
        Matrix.posSemidef_vecMulVec_self_star (fun i => x i)
    have ht := h _ hv
    rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
      dotProduct_comm, euclidean_dotProduct_matrix] at ht
    rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
      dotProduct_comm, euclidean_dotProduct_matrix] at ht
    exact ht
  have hD := Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.sub hB)
  have hLin : (A - B).toEuclideanLin = 0 := hD.inner_map_self_eq_zero.mp (fun x => by
    rw [map_sub, LinearMap.sub_apply, inner_sub_left,
      real_inner_comm x (A.toEuclideanLin x), real_inner_comm x (B.toEuclideanLin x), hq]
    exact sub_self _)
  apply sub_eq_zero.mp
  apply (Matrix.toLpLin 2 2).injective
  simpa only [map_zero] using hLin

noncomputable def positiveLaplaceKernel {p : ℕ} (T : positiveMatrixMonoid p) :
    positiveMatrixMonoid p →ᵇ ℝ where
  toFun W := Real.exp (-Matrix.trace (T.val * W.val))
  continuous_toFun := by fun_prop
  map_bounded' := by
    refine ⟨2, fun W V => ?_⟩
    have hbound (X : positiveMatrixMonoid p) :
        ‖Real.exp (-Matrix.trace (T.val * X.val))‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (trace_positive_product T.2 X.2))
    exact (dist_le_norm_add_norm _ _).trans (by linarith [hbound W, hbound V])

theorem positiveLaplaceKernel_zero {p : ℕ} :
    positiveLaplaceKernel (0 : positiveMatrixMonoid p) = 1 := by
  ext W
  simp [positiveLaplaceKernel]

theorem positiveLaplaceKernel_add {p : ℕ} (S T : positiveMatrixMonoid p) :
    positiveLaplaceKernel (S + T) = positiveLaplaceKernel S * positiveLaplaceKernel T := by
  ext W
  simp [positiveLaplaceKernel, Matrix.add_mul, Matrix.trace_add, Real.exp_add, mul_comm]

theorem positiveLaplaceKernel_separates {p : ℕ} (W V : positiveMatrixMonoid p)
    (hWV : W ≠ V) : ∃ T, positiveLaplaceKernel T W ≠ positiveLaplaceKernel T V := by
  contrapose! hWV
  apply Subtype.ext
  apply hermitian_eq_of_positive_trace W.2.1 V.2.1
  intro T hT
  exact neg_injective (Real.exp_injective (hWV ⟨T, hT⟩))

theorem positive_matrix_measure_eq_of_laplace {p : ℕ}
    {μ ν : Measure (positiveMatrixMonoid p)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ T : positiveMatrixMonoid p,
      ∫ W, Real.exp (-Matrix.trace (T.val * W.val)) ∂μ =
        ∫ W, Real.exp (-Matrix.trace (T.val * W.val)) ∂ν) : μ = ν :=
  measure_eq_of_kernel_integrals positiveLaplaceKernel positiveLaplaceKernel_zero
    positiveLaplaceKernel_add positiveLaplaceKernel_separates h

theorem matrix_measure_eq_of_positive_laplace {p : ℕ}
    {μ ν : Measure (Matrix (Fin p) (Fin p) ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ W ∂μ, W.PosSemidef) (hν : ∀ᵐ W ∂ν, W.PosSemidef)
    (h : ∀ T : Matrix (Fin p) (Fin p) ℝ, T.PosSemidef →
      ∫ W, Real.exp (-Matrix.trace (T * W)) ∂μ =
        ∫ W, Real.exp (-Matrix.trace (T * W)) ∂ν) : μ = ν := by
  have hs : MeasurableSet {W : Matrix (Fin p) (Fin p) ℝ | W.PosSemidef} :=
    Matrix.posSemidef_is_closed.measurableSet
  have hμr : μ.restrict {W : Matrix (Fin p) (Fin p) ℝ | W.PosSemidef} = μ :=
    Measure.restrict_eq_self_of_ae_mem
      (s := {W : Matrix (Fin p) (Fin p) ℝ | W.PosSemidef}) hμ
  have hνr : ν.restrict {W : Matrix (Fin p) (Fin p) ℝ | W.PosSemidef} = ν :=
    Measure.restrict_eq_self_of_ae_mem
      (s := {W : Matrix (Fin p) (Fin p) ℝ | W.PosSemidef}) hν
  let μ₀ : Measure (positiveMatrixMonoid p) := μ.comap Subtype.val
  let ν₀ : Measure (positiveMatrixMonoid p) := ν.comap Subtype.val
  have hμi (T : positiveMatrixMonoid p) :
      (∫ W, Real.exp (-Matrix.trace (T.val * W.val)) ∂μ₀) =
        ∫ W, Real.exp (-Matrix.trace (T.val * W)) ∂μ := by
    calc
      _ = ∫ W in {W : Matrix (Fin p) (Fin p) ℝ | W.PosSemidef},
          Real.exp (-Matrix.trace (T.val * W)) ∂μ :=
        integral_subtype_comap hs (fun W => Real.exp (-Matrix.trace (T.val * W)))
      _ = _ := by rw [hμr]
  have hνi (T : positiveMatrixMonoid p) :
      (∫ W, Real.exp (-Matrix.trace (T.val * W.val)) ∂ν₀) =
        ∫ W, Real.exp (-Matrix.trace (T.val * W)) ∂ν := by
    calc
      _ = ∫ W in {W : Matrix (Fin p) (Fin p) ℝ | W.PosSemidef},
          Real.exp (-Matrix.trace (T.val * W)) ∂ν :=
        integral_subtype_comap hs (fun W => Real.exp (-Matrix.trace (T.val * W)))
      _ = _ := by rw [hνr]
  have he : μ₀ = ν₀ := by
    apply positive_matrix_measure_eq_of_laplace
    intro T
    rw [hμi, hνi]
    exact h T.val T.2
  calc
    μ = μ.restrict {W : Matrix (Fin p) (Fin p) ℝ | W.PosSemidef} :=
      hμr.symm
    _ = μ₀.map Subtype.val := (map_comap_subtype_coe hs μ).symm
    _ = ν₀.map Subtype.val := congrArg (fun ρ : Measure (positiveMatrixMonoid p) => ρ.map Subtype.val) he
    _ = ν.restrict {W : Matrix (Fin p) (Fin p) ℝ | W.PosSemidef} := map_comap_subtype_coe hs ν
    _ = ν := hνr

end ResearchMain.WishartBlocks


