import MainTheorems.WishartBlocks.RegularizedExpectationODE
import Mathlib.Analysis.SpecificLimits.Basic

namespace ResearchMain.WishartBlocks

open Matrix MeasureTheory Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

noncomputable def regularizationScale (N : ℕ) : ℝ := ((N : ℝ) + 1)⁻¹

theorem regularizationScale_pos (N : ℕ) : 0 < regularizationScale N := by
  unfold regularizationScale
  positivity

theorem regularizationScale_le_one (N : ℕ) : regularizationScale N ≤ 1 := by
  unfold regularizationScale
  exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])

theorem regularizationScale_tendsto :
    Tendsto regularizationScale atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop))

theorem oneRowWishart_real_growth_integrable {p : ℕ} {q : ℝ} (hq : (p : ℝ) < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (m : EuclideanSpace ℝ (Fin p)) {f : Matrix (Fin p) (Fin p) ℝ → ℝ}
    (hf : Measurable f) {C β : ℝ} (hC : 0 ≤ C)
    (hB : ∀ W, ‖f W‖ ≤ C * (1 + ‖W‖) ^ β) :
    Integrable f (oneRowWishartLaw q S m) := by
  rw [oneRowWishart_as_noncentral hq hS]
  exact noncentralWishart_real_growth_integrable (by norm_num; linarith) S _ hf hC hB

namespace BlockPartition

noncomputable def uniformShiftConstant {p d : ℕ} (P : BlockPartition p d)
    (K : ∀ j, Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ) (ν : Fin d → ℝ) : ℝ :=
  ∏ j, (Fintype.card (Equiv.Perm (Fin (P.size j))) *
    (1 + ‖K j‖ + ‖(1 : Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ)‖) ^ P.size j) ^ ν j

theorem uniformShiftConstant_nonneg {p d : ℕ} (P : BlockPartition p d)
    (K : ∀ j, Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ) (ν : Fin d → ℝ) :
    0 ≤ P.uniformShiftConstant K ν :=
  Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by positivity) _

theorem regularizedShift_growth {p d : ℕ} (P : BlockPartition p d)
    (K : ∀ j, Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ) (ν : Fin d → ℝ)
    (hν : ∀ j, 0 ≤ ν j) (N : ℕ) (W : Matrix (Fin p) (Fin p) ℝ) :
    ‖P.shiftedDeterminantProduct (fun j => K j + regularizationScale N • 1) ν W‖ ≤
      P.uniformShiftConstant K ν * (1 + ‖W‖) ^ P.productGrowthExponent ν := by
  have hK (j : Fin d) : ‖K j + regularizationScale N • 1‖ ≤
      ‖K j‖ + ‖(1 : Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ)‖ := by
    apply (norm_add_le _ _).trans
    rw [norm_smul, Real.norm_of_nonneg (regularizationScale_pos N).le]
    exact add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg _) (regularizationScale_le_one N))
  apply (P.shiftedDeterminantProduct_growth _ ν hν W).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  apply Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (by positivity) _)
  intro j _
  apply Real.rpow_le_rpow (by positivity) _ (hν j)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by linarith [hK j]) _

theorem regularizedShift_tendsto {p d : ℕ} (P : BlockPartition p d)
    (K : ∀ j, Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ) (ν : Fin d → ℝ)
    (hν : ∀ j, 0 ≤ ν j) (W : Matrix (Fin p) (Fin p) ℝ) :
    Tendsto (fun N => P.shiftedDeterminantProduct (fun j => K j + regularizationScale N • 1) ν W)
      atTop (𝓝 (P.shiftedDeterminantProduct K ν W)) := by
  apply tendsto_finsetProd
  intro j _
  have hM : Tendsto (fun N => P.block W j + (K j + regularizationScale N • 1))
      atTop (𝓝 (P.block W j + K j)) := by
    simpa only [zero_smul, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.add (regularizationScale_tendsto.smul_const
        (1 : Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ)))
  have hd : Continuous (fun A : Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ => A.det) :=
    continuous_id.matrix_det
  exact ((Real.continuous_rpow_const (hν j)).comp hd).tendsto
    (P.block W j + K j) |>.comp hM

theorem oneRowWishart_shiftedProduct_integrable {p d : ℕ} (P : BlockPartition p d)
    (K : ∀ j, Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ) (ν : Fin d → ℝ)
    (hν : ∀ j, 0 ≤ ν j) {q : ℝ} (hq : (p : ℝ) < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (m : EuclideanSpace ℝ (Fin p)) :
    Integrable (P.shiftedDeterminantProduct K ν) (oneRowWishartLaw q S m) := by
  rw [oneRowWishart_as_noncentral hq hS]
  exact P.noncentral_shiftedDeterminantProduct_integrable (by norm_num; linarith) S _ K ν hν

theorem oneRowWishart_regularizedShift_integral_tendsto {p d : ℕ} (P : BlockPartition p d)
    (K : ∀ j, Matrix (Fin (P.size j)) (Fin (P.size j)) ℝ) (ν : Fin d → ℝ)
    (hν : ∀ j, 0 ≤ ν j) {q : ℝ} (hq : (p : ℝ) < q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (m : EuclideanSpace ℝ (Fin p)) :
    Tendsto (fun N => ∫ W, P.shiftedDeterminantProduct
      (fun j => K j + regularizationScale N • 1) ν W ∂(oneRowWishartLaw q S m)) atTop
      (𝓝 (∫ W, P.shiftedDeterminantProduct K ν W ∂(oneRowWishartLaw q S m))) := by
  apply tendsto_integral_of_dominated_convergence
    (fun W => P.uniformShiftConstant K ν * (1 + ‖W‖) ^ P.productGrowthExponent ν)
  · intro N
    exact (P.measurable_shiftedDeterminantProduct _ ν).aestronglyMeasurable
  · apply oneRowWishart_real_growth_integrable hq hS m (by fun_prop)
      (P.uniformShiftConstant_nonneg K ν)
    intro W
    rw [Real.norm_of_nonneg (mul_nonneg (P.uniformShiftConstant_nonneg K ν)
      (Real.rpow_nonneg (by positivity) _))]
  · intro N
    exact ae_of_all _ fun W => P.regularizedShift_growth K ν hν N W
  · exact ae_of_all _ fun W => P.regularizedShift_tendsto K ν hν W

theorem gaussianProductExpectation_re_actualLaw {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) {ε q : ℝ} (hε : 0 < ε)
    (S : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    (P.gaussianProductExpectation ν ε q S v s).re =
      ∫ W, P.shiftedDeterminantProduct (fun _ => ε • 1) ν W
        ∂(oneRowWishartLaw q S (s • v)) := by
  rw [P.gaussianProductExpectation_actualLaw (hε := hε)]
  have he : (fun W => (P.smoothRegularizedProduct ν ε W : ℂ)) =ᵐ[
      oneRowWishartLaw q S (s • v)] (fun W => (P.shiftedDeterminantProduct
        (fun _ => ε • 1) ν W : ℂ)) := by
    filter_upwards [oneRowWishart_positiveSemidefinite q S (s • v)] with W hW
    rw [P.smoothRegularizedProduct_eq ν hε hW]
    rfl
  rw [integral_congr_ae he, integral_complex_ofReal]
  rfl

theorem rankOne_determinantProduct_monotone {p d : ℕ} (P : BlockPartition p d)
    (ν : Fin d → ℝ) (hν : ∀ j, 0 ≤ ν j) {q : ℝ}
    (hq : (p : ℝ) < q) (hq₁ : 1 < q) (hqB : ∀ j, (P.size j : ℝ) + 1 ≤ q)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (v : EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun θ => ∫ W, P.determinantProduct ν W
      ∂(oneRowWishartLaw q S (Real.sqrt θ • v))) (Set.Ici 0) := by
  intro θ hθ η hη hθη
  apply le_of_tendsto_of_tendsto
    (by simpa only [shiftedDeterminantProduct, determinantProduct, determinantPower, add_zero] using
      P.oneRowWishart_regularizedShift_integral_tendsto (fun _ => 0) ν hν hq hS (Real.sqrt θ • v))
    (by simpa only [shiftedDeterminantProduct, determinantProduct, determinantPower, add_zero] using
      P.oneRowWishart_regularizedShift_integral_tendsto (fun _ => 0) ν hν hq hS (Real.sqrt η • v))
  exact Eventually.of_forall fun N => by
    have h := P.regularizedProduct_mean_ray_monotone ν hν (regularizationScale_pos N)
        hq hq₁ hqB hS v hθ hη hθη
    change (P.gaussianProductExpectation ν (regularizationScale N) q S v (Real.sqrt θ)).re ≤
      (P.gaussianProductExpectation ν (regularizationScale N) q S v (Real.sqrt η)).re at h
    rw [P.gaussianProductExpectation_re_actualLaw ν (regularizationScale_pos N),
      P.gaussianProductExpectation_re_actualLaw ν (regularizationScale_pos N)] at h
    simpa only [shiftedDeterminantProduct, zero_add] using h

end BlockPartition
end ResearchMain.WishartBlocks

