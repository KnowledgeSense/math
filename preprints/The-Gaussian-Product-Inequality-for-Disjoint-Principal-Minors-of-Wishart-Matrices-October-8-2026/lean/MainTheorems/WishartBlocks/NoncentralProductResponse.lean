import MainTheorems.WishartBlocks.TranslatedRegularizedProduct
import MainTheorems.WishartBlocks.NoncentralDeterminantResponse

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators MatrixOrder InnerProductSpace

namespace BlockPartition

noncomputable def noncentralProductResponse {p k d : ℕ} (P : BlockPartition p d) (α : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (K : Matrix (Fin k) (Fin p) ℝ) (ν : Fin d → ℝ)
    (W : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  ∫ B, P.determinantProduct ν B ∂(noncentralWishartLaw α S (covarianceMeanRows W K))

theorem augmentedOneRow_product_integrable {p r d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {q : ℝ} (hq : (p : ℝ) < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (m : EuclideanSpace ℝ (Fin p)) (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    Integrable (P.determinantProduct ν) (augmentedOneRowLaw q S m M) := by
  rw [noncentralWishart_cons_row hq hS m M]
  exact P.noncentral_determinantProduct_integrable (by push_cast; linarith) S _ ν hν

theorem augmentedOneRow_product_monotone {p r d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {q : ℝ} (hq : (p : ℝ) < q) (hq₁ : 1 < q)
    (hqB : ∀ j, (P.size j : ℝ) + 1 ≤ q) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (v : EuclideanSpace ℝ (Fin p)) (M : Fin r → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun θ => ∫ B, P.determinantProduct ν B
      ∂(augmentedOneRowLaw q S (Real.sqrt θ • v) M)) (Set.Ici 0) := by
  let γ := Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin p))
  let F := fun wz : Matrix (Fin p) (Fin p) ℝ × (Fin r → EuclideanSpace ℝ (Fin p)) =>
    P.determinantProduct ν (noncentralWishartValue S M wz)
  have hi : ∀ θ, Integrable F ((oneRowWishartLaw q S (Real.sqrt θ • v)).prod γ) := by
    intro θ
    have h := P.augmentedOneRow_product_integrable ν hν hq hS (Real.sqrt θ • v) M
    unfold augmentedOneRowLaw at h
    exact (integrable_map_measure (P.measurable_determinantProduct ν).aestronglyMeasurable
      (measurable_noncentralWishartValue S M).aemeasurable).mp h
  have he : ∀ θ, (∫ B, P.determinantProduct ν B
      ∂(augmentedOneRowLaw q S (Real.sqrt θ • v) M)) =
      ∫ z : Fin r → EuclideanSpace ℝ (Fin p), ∫ B,
        P.shiftedDeterminantProduct (fun j => P.block (∑ i, gaussianMeanGram S (M i) (z i)) j) ν B
          ∂(oneRowWishartLaw q S (Real.sqrt θ • v)) ∂γ := by
    intro θ
    let : IsProbabilityMeasure (oneRowWishartLaw q S (Real.sqrt θ • v)) :=
      oneRowWishart_probability hq S (Real.sqrt θ • v)
    unfold augmentedOneRowLaw
    rw [integral_map (measurable_noncentralWishartValue S M).aemeasurable
      (P.measurable_determinantProduct ν).aestronglyMeasurable]
    have h := integral_prod_symm F (hi θ)
    simpa only [F, determinantProduct, determinantPower, shiftedDeterminantProduct,
      noncentralWishartValue, block, Matrix.submatrix_add, Pi.add_apply] using h
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
    simpa only [gaussianMeanGram, star_trivial] using Matrix.posSemidef_vecMulVec_self_star
      (fun j => ((CFC.sqrt S).toEuclideanLin (z i) + M i) j)
  exact P.rankOne_shifted_product_monotone ν hν hq hq₁ hqB hS hK v hθ hη hθη

theorem noncentralProductResponse_rankOne {p n d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {α c : ℝ}
    (hα : (p : ℝ) - 1 < α - ((n + 1 : ℕ) : ℝ)) (hc : 0 ≤ c)
    (hq₁ : 1 < α - (n : ℝ)) (hqB : ∀ j, (P.size j : ℝ) + 1 ≤ α - (n : ℝ))
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (K : Matrix (Fin (n + 1)) (Fin p) ℝ)
    {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hW : W.PosDef)
    (u : EuclideanSpace ℝ (Fin (n + 1))) :
    P.noncentralProductResponse α S K ν W ≤ P.noncentralProductResponse α S K ν
      (W + c • Matrix.vecMulVec (fun i => u i) (fun i => u i)) := by
  by_cases hu : u = 0
  · have hz : Matrix.vecMulVec (fun i => u i) (fun i => u i) = 0 := by
      rw [hu]
      ext i j
      simp only [Matrix.vecMulVec_apply, PiLp.zero_apply, zero_mul, Matrix.zero_apply]
    rw [hz, smul_zero, add_zero]
  obtain ⟨θ, M, hθ, hGram⟩ := rankOne_gram_factor hW K u hu
  let v := K.transpose.toLpLin 2 2 u
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
    have hs : ∀ t ≥ 0, Matrix.vecMulVec (fun i => (Real.sqrt t • v) i)
        (fun i => (Real.sqrt t • v) i) = t • Matrix.vecMulVec (fun i => v i) (fun i => v i) := by
      intro t ht
      ext i j
      simp only [Matrix.vecMulVec_apply, PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply]
      calc
        (Real.sqrt t * v i) * (Real.sqrt t * v j) = (Real.sqrt t) ^ 2 * (v i * v j) := by ring
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
  unfold noncentralProductResponse
  rw [he, he']
  exact P.augmentedOneRow_product_monotone ν hν hq hq₁ hqB hS v M hθ.le
    (add_nonneg hθ.le hc) (by linarith)

theorem noncentralProductResponse_monotone {p n d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {α : ℝ}
    (hα : (p : ℝ) - 1 < α - ((n + 1 : ℕ) : ℝ))
    (hq₁ : 1 < α - (n : ℝ)) (hqB : ∀ j, (P.size j : ℝ) + 1 ≤ α - (n : ℝ))
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (K : Matrix (Fin (n + 1)) (Fin p) ℝ) :
    MonotoneOn (P.noncentralProductResponse α S K ν) {W | W.PosDef} := by
  apply monotoneOn_positiveDefinite_of_rankOne
  intro W hW u
  simpa only [one_smul] using P.noncentralProductResponse_rankOne ν hν hα
    (by norm_num : (0 : ℝ) ≤ 1) hq₁ hqB hS K hW u

end BlockPartition
end ResearchMain.WishartBlocks
