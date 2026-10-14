import MainTheorems.WishartBlocks.RankOneDeterminantMonotonicity
import MainTheorems.WishartBlocks.RankOneGramFactor

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder InnerProductSpace Matrix.Norms.Elementwise

noncomputable def covarianceMeanRows {p k : ℕ} (W : Matrix (Fin k) (Fin k) ℝ)
    (K : Matrix (Fin k) (Fin p) ℝ) : Fin k → EuclideanSpace ℝ (Fin p) :=
  fun i => WithLp.toLp 2 (((CFC.sqrt W).transpose * K) i)

theorem covarianceMeanRows_gram {p k : ℕ} {W : Matrix (Fin k) (Fin k) ℝ}
    (hW : W.PosSemidef) (K : Matrix (Fin k) (Fin p) ℝ) :
    meanRowGram (covarianceMeanRows W K) = K.transpose * W * K := by
  unfold covarianceMeanRows
  rw [matrix_rows_gram, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hR : (CFC.sqrt W).transpose = CFC.sqrt W := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg W).posSemidef.1.eq
  rw [hR]
  have he := CFC.sqrt_mul_sqrt_self W hW.nonneg
  simpa only [Matrix.mul_assoc] using congrArg (fun X => K.transpose * X * K) he

noncomputable def noncentralDeterminantResponse {p k : ℕ} (α : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (K : Matrix (Fin k) (Fin p) ℝ) (b : ℝ)
    (W : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  ∫ B : Matrix (Fin p) (Fin p) ℝ, B.det ^ b
    ∂(noncentralWishartLaw α S (covarianceMeanRows W K))

theorem augmentedOneRow_determinant_integrable {p r : ℕ} {q b : ℝ}
    (hq : (p : ℝ) < q) (hb : 0 ≤ b) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (m : EuclideanSpace ℝ (Fin p)) (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    Integrable (fun B : Matrix (Fin p) (Fin p) ℝ => B.det ^ b) (augmentedOneRowLaw q S m M) := by
  rw [noncentralWishart_cons_row hq hS m M]
  apply noncentralWishart_real_growth_integrable
    (C := (Fintype.card (Equiv.Perm (Fin p)) : ℝ) ^ b) (β := (p : ℝ) * b)
    (by push_cast; linarith) S _ (by fun_prop)
    (Real.rpow_nonneg (by positivity) b)
  intro W
  simpa only [Matrix.submatrix_id_id, add_zero, norm_zero, add_zero, one_pow, mul_one] using
    determinant_shift_power_growth id (0 : Matrix (Fin p) (Fin p) ℝ) W hb

theorem augmentedOneRow_determinant_monotone {p r : ℕ} {q b : ℝ}
    (hq : (p : ℝ) < q) (hb : 0 ≤ b) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (v : EuclideanSpace ℝ (Fin p)) (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn
      (fun θ => ∫ B : Matrix (Fin p) (Fin p) ℝ, B.det ^ b
        ∂(augmentedOneRowLaw q S (Real.sqrt θ • v) M)) (Set.Ici 0) := by
  let γ := Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin p))
  let F := fun (wz : Matrix (Fin p) (Fin p) ℝ × (Fin r → EuclideanSpace ℝ (Fin p))) =>
    (noncentralWishartValue S M wz).det ^ b
  have hg : Measurable (fun B : Matrix (Fin p) (Fin p) ℝ => B.det ^ b) := by fun_prop
  have hi : ∀ θ, Integrable F ((oneRowWishartLaw q S (Real.sqrt θ • v)).prod γ) := by
    intro θ
    have h := augmentedOneRow_determinant_integrable hq hb hS (Real.sqrt θ • v) M
    unfold augmentedOneRowLaw at h
    exact (integrable_map_measure hg.aestronglyMeasurable
      (measurable_noncentralWishartValue S M).aemeasurable).mp h
  have he : ∀ θ,
      (∫ B : Matrix (Fin p) (Fin p) ℝ, B.det ^ b
        ∂(augmentedOneRowLaw q S (Real.sqrt θ • v) M)) =
      ∫ z : Fin r → EuclideanSpace ℝ (Fin p),
        ∫ B, (B + ∑ i, gaussianMeanGram S (M i) (z i)).det ^ b
          ∂(oneRowWishartLaw q S (Real.sqrt θ • v)) ∂γ := by
    intro θ
    let : IsProbabilityMeasure (oneRowWishartLaw q S (Real.sqrt θ • v)) :=
      oneRowWishart_probability hq S (Real.sqrt θ • v)
    unfold augmentedOneRowLaw
    rw [integral_map (measurable_noncentralWishartValue S M).aemeasurable
      hg.aestronglyMeasurable]
    exact integral_prod_symm F (hi θ)
  intro θ hθ η hη hθη
  let : IsProbabilityMeasure (oneRowWishartLaw q S (Real.sqrt θ • v)) :=
    oneRowWishart_probability hq S (Real.sqrt θ • v)
  let : IsProbabilityMeasure (oneRowWishartLaw q S (Real.sqrt η • v)) :=
    oneRowWishart_probability hq S (Real.sqrt η • v)
  dsimp only
  rw [he θ, he η]
  apply integral_mono (hi θ).integral_prod_right (hi η).integral_prod_right
  intro z
  have hK : (∑ i, gaussianMeanGram S (M i) (z i)).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    simpa only [gaussianMeanGram, star_trivial] using
      Matrix.posSemidef_vecMulVec_self_star
        (fun j => ((CFC.sqrt S).toEuclideanLin (z i) + M i) j)
  exact rankOne_shifted_determinant_monotone hq hb hS hK v hθ hη hθη

theorem noncentralDeterminantResponse_rankOne {p n : ℕ} {α b c : ℝ}
    (hα : (p : ℝ) - 1 < α - ((n + 1 : ℕ) : ℝ)) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (K : Matrix (Fin (n + 1)) (Fin p) ℝ)
    {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hW : W.PosDef)
    (u : EuclideanSpace ℝ (Fin (n + 1))) :
    noncentralDeterminantResponse α S K b W ≤
      noncentralDeterminantResponse α S K b
        (W + c • Matrix.vecMulVec (fun i => u i) (fun i => u i)) := by
  by_cases hu : u = 0
  · have hz : Matrix.vecMulVec (fun i => u i) (fun i => u i) = 0 := by
      rw [hu]
      ext i j
      simp only [Matrix.vecMulVec_apply, PiLp.zero_apply, zero_mul, Matrix.zero_apply]
    rw [hz, smul_zero, add_zero]
  obtain ⟨θ, M, hθ, hGram⟩ := rankOne_gram_factor hW K u hu
  let v := (K.transpose.toLpLin 2 2) u
  let q := α - (n : ℝ)
  have hq : (p : ℝ) < q := by dsimp [q]; push_cast at hα; linarith
  have hα' : α = q + (n : ℝ) := by dsimp [q]; ring
  have hW' : (W + c • Matrix.vecMulVec (fun i => u i) (fun i => u i)).PosDef := by
    apply hW.add_posSemidef
    apply Matrix.PosSemidef.smul _ hc
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (fun i => u i)
  have hGram' : meanRowGram (Fin.cons (Real.sqrt (θ + c) • v) M) =
      K.transpose * (W + c • Matrix.vecMulVec (fun i => u i) (fun i => u i)) * K := by
    rw [meanRowGram_cons, rankOne_gram_increment]
    rw [meanRowGram_cons] at hGram
    have hs : ∀ t ≥ 0,
        Matrix.vecMulVec (fun i => (Real.sqrt t • v) i) (fun i => (Real.sqrt t • v) i) =
          t • Matrix.vecMulVec (fun i => v i) (fun i => v i) := by
      intro t ht
      ext i j
      simp only [Matrix.vecMulVec_apply, PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply]
      calc
        (Real.sqrt t * v i) * (Real.sqrt t * v j) =
            (Real.sqrt t) ^ 2 * (v i * v j) := by ring
        _ = _ := by rw [Real.sq_sqrt ht]
    rw [hs θ hθ.le] at hGram
    rw [hs (θ + c) (by positivity), ← hGram]
    module
  have he : noncentralWishartLaw α S (covarianceMeanRows W K) =
      augmentedOneRowLaw q S (Real.sqrt θ • v) M := by
    rw [noncentralWishart_cons_row hq hS, ← hα']
    apply noncentralWishart_meanGram_eq hα hα hS
    rw [covarianceMeanRows_gram hW.posSemidef, hGram]
  have he' : noncentralWishartLaw α S
        (covarianceMeanRows (W + c • Matrix.vecMulVec (fun i => u i) (fun i => u i)) K) =
      augmentedOneRowLaw q S (Real.sqrt (θ + c) • v) M := by
    rw [noncentralWishart_cons_row hq hS, ← hα']
    apply noncentralWishart_meanGram_eq hα hα hS
    rw [covarianceMeanRows_gram hW'.posSemidef, hGram']
  unfold noncentralDeterminantResponse
  rw [he, he']
  exact augmentedOneRow_determinant_monotone hq hb hS v M hθ.le
    (add_nonneg hθ.le hc) (by linarith)

end ResearchMain.WishartBlocks
