import EdgeColoringMixing.BufferNorm
import EdgeColoringMixing.Derivatives
import EdgeColoringMixing.ColumnBlocks
import EdgeColoringMixing.PosteriorMoments
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false

/-! The actual weighted-injection Jacobian and the retained-column covariance
transfer in the arcsine metric. All cell coordinates are retained; zero weights
are treated by the same zero-inverse convention as the paper. -/
namespace EdgeColoringMixing
open Finset Matrix WeightedInjection

namespace WeightedInjection
variable {d q : ℕ}

/-- The negative rank-one column blocks imply the exact diagonal majorant. -/
theorem columnBlock_le_diagonal (μ : FiniteLaw (Injection d q)) :
    (Matrix.diagonal (fun x : Fin d × Fin q => mean μ x.1 x.2) - columnBlock μ).PosSemidef := by
  let v : Fin q → (Fin d × Fin q) → ℝ := fun c x => if x.2 = c then mean μ x.1 x.2 else 0
  have heq : Matrix.diagonal (fun x : Fin d × Fin q => mean μ x.1 x.2) - columnBlock μ =
      ∑ c, Matrix.vecMulVec (v c) (v c) := by
    ext x y
    simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.vecMulVec, v]
    by_cases hxy : x.2 = y.2
    · simp [columnBlock, hxy, Matrix.diagonal_apply, Prod.ext_iff]
    · simp [columnBlock, hxy, Matrix.diagonal_apply]
      intro h
      exact False.elim (hxy (congrArg Prod.snd h))
  rw [heq]
  apply Matrix.posSemidef_sum
  intro c _
  simpa using Matrix.posSemidef_vecMulVec_self_star (v c)

/-- The exact covariance action in one availability step. -/
noncomputable def colorCovarianceAction (μ : FiniteLaw (Injection d q))
    (v : Fin d × Fin q → ℝ) : Fin q → ℝ :=
  columnSum *ᵥ (covariance μ *ᵥ v)

/-- Covariance domination transfers to the weighted output norm. This is a
quadratic-form proof of the noncommutative scalar spectral transfer. -/
theorem colorCovarianceAction_bound (μ : FiniteLaw (Injection d q)) {β : ℝ}
    (hβ : 0 ≤ β) (hcov : (β • columnBlock μ - covariance μ).PosSemidef)
    (v : Fin d × Fin q → ℝ) :
    (∑ c, colorCovarianceAction μ v c ^ 2 / (colorMean μ c * (1 - colorMean μ c))) ≤
      β * (v ⬝ᵥ covariance μ *ᵥ v) := by
  let y := colorCovarianceAction μ v
  let V := fun c => colorMean μ c * (1 - colorMean μ c)
  let E := ∑ c, y c ^ 2 / V c
  let z := fun c => y c / V c
  let u : Fin d × Fin q → ℝ := columnSumᵀ *ᵥ z
  have hV (c : Fin q) : 0 ≤ V c :=
    mul_nonneg (colorMean_nonneg μ c) (by linarith [colorMean_le_one μ c])
  have hE : 0 ≤ E := sum_nonneg (fun c _ => div_nonneg (sq_nonneg _) (hV c))
  have hz : z ⬝ᵥ y = E := by
    unfold dotProduct
    apply sum_congr rfl
    intro c _
    dsimp only [z]
    ring
  have hmix : u ⬝ᵥ covariance μ *ᵥ v = E := by
    change (columnSumᵀ *ᵥ z) ⬝ᵥ covariance μ *ᵥ v = E
    rw [← vecMul_transpose columnSumᵀ z, transpose_transpose, ← dotProduct_mulVec]
    exact hz
  have hBB : u ⬝ᵥ columnBlock μ *ᵥ u = E := by
    change (columnSumᵀ *ᵥ z) ⬝ᵥ columnBlock μ *ᵥ (columnSumᵀ *ᵥ z) = E
    rw [← vecMul_transpose columnSumᵀ z, transpose_transpose, ← dotProduct_mulVec]
    rw [← mulVec_transpose]
    simp only [mulVec_mulVec]
    rw [← Matrix.mul_assoc, column_variance_identity]
    simp only [mulVec_diagonal, dotProduct]
    apply sum_congr rfl
    intro c _
    dsimp only [z, V]
    by_cases hc : colorMean μ c * (1 - colorMean μ c) = 0
    · simp [hc]
    · field_simp
  have hu : u ⬝ᵥ covariance μ *ᵥ u ≤ β * E := by
    have h := hcov.dotProduct_mulVec_nonneg u
    simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, hBB] at h
    linarith
  have hv : 0 ≤ v ⬝ᵥ covariance μ *ᵥ v := by
    simpa using (covariance_posSemidef μ).dotProduct_mulVec_nonneg v
  have hcs := semidefinite_cauchy_schwarz (covariance_posSemidef μ) u v
  rw [hmix] at hcs
  have hh := mul_le_mul_of_nonneg_right hu hv
  change E ≤ β * (v ⬝ᵥ covariance μ *ᵥ v)
  by_cases he : E = 0
  · rw [he]
    exact mul_nonneg hβ hv
  · have hpos : 0 < E := lt_of_le_of_ne hE (Ne.symm he)
    nlinarith

/-- The same hypothesis also gives the diagonal input-energy estimate. -/
theorem covariance_input_bound (μ : FiniteLaw (Injection d q)) {β : ℝ}
    (hβ : 0 ≤ β) (hcov : (β • columnBlock μ - covariance μ).PosSemidef)
    (v : Fin d × Fin q → ℝ) :
    v ⬝ᵥ covariance μ *ᵥ v ≤ β * ∑ x, mean μ x.1 x.2 * v x ^ 2 := by
  have h := ((columnBlock_le_diagonal μ).smul hβ).add hcov
  have hh := h.dotProduct_mulVec_nonneg v
  simp only [star_trivial, add_mulVec, sub_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hh
  have heq : v ⬝ᵥ Matrix.diagonal (fun x : Fin d × Fin q => mean μ x.1 x.2) *ᵥ v =
      ∑ x, mean μ x.1 x.2 * v x ^ 2 := by
    simp only [mulVec_diagonal, dotProduct]
    apply sum_congr rfl
    intro x _
    ring
  rw [heq] at hh
  linarith

theorem colorCovarianceAction_apply (μ : FiniteLaw (Injection d q))
    (v : Fin d × Fin q → ℝ) (a : Fin q) :
    colorCovarianceAction μ v a = ∑ i, ∑ x, covariance μ (i,a) x * v x := by
  simp [colorCovarianceAction, Matrix.mulVec, dotProduct, columnSum, Fintype.sum_prod_type]

/-- A zero column of the law gives a genuinely zero output tangent. -/
theorem colorCovarianceAction_zero (μ : FiniteLaw (Injection d q))
    (v : Fin d × Fin q → ℝ) (a : Fin q) (hz : ∀ i, mean μ i a = 0) :
    colorCovarianceAction μ v a = 0 := by
  rw [colorCovarianceAction_apply]
  apply sum_eq_zero
  intro i _
  apply sum_eq_zero
  intro x _
  have hc : covariance μ (i,a) x = 0 := by
    rw [covariance, FiniteLaw.covariance_symm]
    exact covariance_eq_zero_of_mean_zero μ x (i,a) (hz i)
  rw [hc, zero_mul]

theorem abs_covariance_cell_le_mean (μ : FiniteLaw (Injection d q))
    (f : Injection d q → ℝ) (hf0 : ∀ σ, 0 ≤ f σ) (hf1 : ∀ σ, f σ ≤ 1)
    (x : Fin d × Fin q) : |μ.covariance f (cell x.1 x.2)| ≤ mean μ x.1 x.2 := by
  have hE0 : 0 ≤ μ.expectation f := μ.expectation_nonneg hf0
  have hE1 : μ.expectation f ≤ 1 := (μ.expectation_mono hf1).trans_eq (μ.expectation_const 1)
  have hP0 : 0 ≤ μ.expectation (fun σ => f σ * cell x.1 x.2 σ) :=
    μ.expectation_nonneg (fun σ => mul_nonneg (hf0 σ) (cell_nonneg _ _ _))
  have hP1 : μ.expectation (fun σ => f σ * cell x.1 x.2 σ) ≤ mean μ x.1 x.2 := by
    apply μ.expectation_mono
    intro σ
    simpa using mul_le_mul_of_nonneg_right (hf1 σ) (cell_nonneg x.1 x.2 σ)
  rw [FiniteLaw.covariance_eq_mixed_moment]
  change |μ.expectation (fun σ => f σ * cell x.1 x.2 σ) -
    μ.expectation f * mean μ x.1 x.2| ≤ mean μ x.1 x.2
  exact abs_le.mpr ⟨by nlinarith [mean_nonneg μ x.1 x.2], by nlinarith [mean_nonneg μ x.1 x.2]⟩

/-- The score of a weight perturbation, on the full finite cell set. -/
noncomputable def injectionScore (v : Fin d × Fin q → ℝ) (σ : Injection d q) : ℝ :=
  ∑ x, v x * cell x.1 x.2 σ

theorem hasDerivAt_weight_path (W : ℝ → Fin d → Fin q → ℝ)
    (ξ : Fin d → Fin q → ℝ) (θ : ℝ)
    (hderiv : ∀ i c, HasDerivAt (fun t => W t i c) (ξ i c) θ)
    (hzero : ∀ i c, W θ i c = 0 → ξ i c = 0) (σ : Injection d q) :
    HasDerivAt (fun t => weight (W t) σ)
      (weight (W θ) σ * injectionScore (fun x => ξ x.1 x.2 / W θ x.1 x.2) σ) θ := by
  have h := HasDerivAt.fun_finsetProd (u := univ) (fun i _ => hderiv i (σ i))
  apply h.congr_deriv
  simp only [smul_eq_mul]
  have hscore : injectionScore (fun x => ξ x.1 x.2 / W θ x.1 x.2) σ =
      ∑ i, ξ i (σ i) / W θ i (σ i) := by
    simp [injectionScore, Fintype.sum_prod_type, cell]
  rw [hscore, Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  by_cases hi : W θ i (σ i) = 0
  · simp [hzero i (σ i) hi]
  · have hp := Finset.mul_prod_erase univ (fun j => W θ j (σ j)) (mem_univ i)
    change (∏ j ∈ univ.erase i, W θ j (σ j)) * ξ i (σ i) =
      (∏ j, W θ j (σ j)) * (ξ i (σ i) / W θ i (σ i))
    rw [← hp]
    field_simp

theorem hasDerivAt_numerator_path (W : ℝ → Fin d → Fin q → ℝ)
    (ξ : Fin d → Fin q → ℝ) (θ : ℝ)
    (hderiv : ∀ i c, HasDerivAt (fun t => W t i c) (ξ i c) θ)
    (hzero : ∀ i c, W θ i c = 0 → ξ i c = 0) (f : Injection d q → ℝ) :
    HasDerivAt (fun t => numerator (W t) f)
      (numerator (W θ) (fun σ => f σ *
        injectionScore (fun x => ξ x.1 x.2 / W θ x.1 x.2) σ)) θ := by
  have h := HasDerivAt.fun_sum (u := univ) (fun σ _ =>
    (hasDerivAt_weight_path W ξ θ hderiv hzero σ).mul_const (f σ))
  apply h.congr_deriv
  unfold numerator
  apply sum_congr rfl
  intro σ _
  ring

/-- Exact differentiation of the normalized law along a path, including zero
weights whose tangent vanishes. No assumption about nearby support is used. -/
theorem hasDerivAt_expectation_path (W : ℝ → Fin d → Fin q → ℝ)
    (ξ : Fin d → Fin q → ℝ) (θ : ℝ)
    (hderiv : ∀ i c, HasDerivAt (fun t => W t i c) (ξ i c) θ)
    (hzero : ∀ i c, W θ i c = 0 → ξ i c = 0)
    (hn : ∀ i c, 0 ≤ W θ i c) (hZ : 0 < partition (W θ)) (f : Injection d q → ℝ) :
    HasDerivAt (fun t => weightedExpectation (W t) f)
      ((law (W θ) hn hZ).covariance f
        (injectionScore (fun x => ξ x.1 x.2 / W θ x.1 x.2))) θ := by
  have hnum := hasDerivAt_numerator_path W ξ θ hderiv hzero f
  have hden : HasDerivAt (fun t => partition (W t))
      (numerator (W θ) (injectionScore (fun x => ξ x.1 x.2 / W θ x.1 x.2))) θ := by
    simpa only [one_mul, numerator, mul_one, partition] using
      hasDerivAt_numerator_path W ξ θ hderiv hzero (fun _ => 1)
  apply (hnum.div hden hZ.ne').congr_deriv
  rw [FiniteLaw.covariance_eq_mixed_moment,
    ← weightedExpectation_eq (W θ) hn hZ,
    ← weightedExpectation_eq (W θ) hn hZ,
    ← weightedExpectation_eq (W θ) hn hZ]
  unfold weightedExpectation
  simp only [numerator]
  field_simp

/-- The score covariance is the finite sum of the actual cell covariances. -/
theorem covariance_injectionScore (μ : FiniteLaw (Injection d q))
    (f : Injection d q → ℝ) (v : Fin d × Fin q → ℝ) :
    μ.covariance f (injectionScore v) =
      ∑ x, μ.covariance f (cell x.1 x.2) * v x := by
  have hfirst : μ.expectation (fun σ => f σ * injectionScore v σ) =
      ∑ x, v x * μ.expectation (fun σ => f σ * cell x.1 x.2 σ) := by
    simp only [injectionScore, Finset.mul_sum, FiniteLaw.expectation_sum]
    apply sum_congr rfl
    intro x _
    rw [← FiniteLaw.expectation_smul]
    congr 1
    ext σ
    ring
  have hsecond : μ.expectation (injectionScore v) =
      ∑ x, v x * μ.expectation (cell x.1 x.2) := by
    unfold injectionScore
    rw [FiniteLaw.expectation_sum]
    simp only [FiniteLaw.expectation_smul]
  simp only [FiniteLaw.covariance_eq_mixed_moment, hfirst, hsecond, Finset.mul_sum,
    sub_mul, Finset.sum_sub_distrib]
  congr 1 <;> apply sum_congr rfl <;> intro x _ <;> ring

/-- Covariance of the unused-color event is precisely the negative column sum. -/
theorem covariance_unused_cell (μ : FiniteLaw (Injection d q))
    (a : Fin q) (x : Fin d × Fin q) :
    μ.covariance (fun σ => if a ∉ Set.range σ then 1 else 0) (cell x.1 x.2) =
      -(∑ i, covariance μ (i,a) x) := by
  classical
  have hf : (fun σ : Injection d q => if a ∉ Set.range σ then (1 : ℝ) else 0) =
      (fun σ => 1 - ∑ i, cell i a σ) := by
    ext σ
    rw [sum_cells_eq_used]
    by_cases ha : a ∈ Set.range σ <;> simp [ha]
  rw [hf]
  simp only [FiniteLaw.covariance_eq_mixed_moment, covariance,
    sub_mul, one_mul, Finset.sum_mul, FiniteLaw.expectation_sub,
    FiniteLaw.expectation_const, FiniteLaw.expectation_sum, Finset.sum_sub_distrib]
  ring

theorem covariance_unused_score (μ : FiniteLaw (Injection d q))
    (a : Fin q) (v : Fin d × Fin q → ℝ) :
    μ.covariance (fun σ => if a ∉ Set.range σ then 1 else 0) (injectionScore v) =
      -colorCovarianceAction μ v a := by
  rw [covariance_injectionScore, colorCovarianceAction_apply]
  simp only [covariance_unused_cell, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- This partition-ratio identity holds even for signed weights, so it can be
used to identify the rational function in an open neighborhood of a path. -/
theorem weightedExpectation_unused (W : Fin d → Fin q → ℝ) (a : Fin q) :
    weightedExpectation W (fun σ => if a ∉ Set.range σ then 1 else 0) =
      partition (withoutColor W a) / partition W := by
  unfold weightedExpectation numerator partition
  congr 1
  apply sum_congr rfl
  intro σ _
  rw [weight_withoutColor]
  by_cases ha : a ∈ Set.range σ <;> simp [ha]

end WeightedInjection

/-- The covariance expression for the genuine directional derivative of `availabilityStep`. -/
noncomputable def availabilityTangent {d q : ℕ} (F : Finset (Fin q))
    (A ξ : Fin d → Fin q → ℝ) {s : ℝ} (hW : RowSurplus (maskedWeights F A) s) :
    Fin q → ℝ :=
  fun c => -colorCovarianceAction (law _ hW.nonneg (partition_pos _ hW))
    (fun x => ξ x.1 x.2 / A x.1 x.2) c

/-- Identification with the derivative of the actual partition-ratio recursion.
The child path is unrestricted near the point; only the zero-coordinate tangent
condition at the point is needed. -/
theorem hasDerivAt_availabilityStep {d q : ℕ} (F : Finset (Fin q))
    (A : ℝ → Fin d → Fin q → ℝ) (ξ : Fin d → Fin q → ℝ) (θ : ℝ) {s : ℝ}
    (hW : RowSurplus (maskedWeights F (A θ)) s)
    (hderiv : ∀ i c, HasDerivAt (fun t => A t i c) (ξ i c) θ)
    (hzero : ∀ i c, A θ i c = 0 → ξ i c = 0) (a : Fin q) :
    HasDerivAt (fun t => availabilityStep F (A t) a)
      (availabilityTangent F (A θ) ξ hW a) θ := by
  classical
  let μ := law _ hW.nonneg (partition_pos _ hW)
  let η := maskedWeights F ξ
  let W := fun t => maskedWeights F (A t)
  let v : Fin d × Fin q → ℝ := fun x => ξ x.1 x.2 / A θ x.1 x.2
  have hm : ∀ i c, HasDerivAt (fun t => W t i c) (η i c) θ := by
    intro i c
    by_cases hc : c ∈ F
    · simpa [W, η, maskedWeights, hc] using hasDerivAt_const θ (0 : ℝ)
    · simpa [W, η, maskedWeights, hc] using hderiv i c
  have hz : ∀ i c, W θ i c = 0 → η i c = 0 := by
    intro i c
    by_cases hc : c ∈ F
    · simp [W, η, maskedWeights, hc]
    · simpa [W, η, maskedWeights, hc] using hzero i c
  have hmask : colorCovarianceAction μ (fun x => η x.1 x.2 / W θ x.1 x.2) =
      colorCovarianceAction μ v := by
    unfold colorCovarianceAction
    congr 1
    funext y
    apply sum_congr rfl
    intro x _
    change covariance μ y x * (η x.1 x.2 / W θ x.1 x.2) = covariance μ y x * v x
    by_cases hx : x.2 ∈ F
    · have hmean : mean μ x.1 x.2 = 0 :=
        mean_eq_zero_of_weight_zero _ hW.nonneg (partition_pos _ hW) x.1 x.2
          (by simp [maskedWeights, hx])
      rw [covariance_eq_zero_of_mean_zero μ y x hmean]
      simp
    · simp [η, W, v, maskedWeights, hx]
  by_cases ha : a ∈ F
  · have hout : availabilityTangent F (A θ) ξ hW a = 0 := by
      unfold availabilityTangent
      change -colorCovarianceAction μ v a = 0
      rw [colorCovarianceAction_zero μ v a (fun i =>
        mean_eq_zero_of_weight_zero _ hW.nonneg (partition_pos _ hW) i a
          (by simp [maskedWeights, ha])), neg_zero]
    rw [hout]
    simpa [availabilityStep, ha] using hasDerivAt_const θ (0 : ℝ)
  · have h := hasDerivAt_expectation_path W η θ hm hz hW.nonneg (partition_pos _ hW)
        (fun σ => if a ∉ Set.range σ then 1 else 0)
    rw [covariance_unused_score, hmask] at h
    simpa only [availabilityStep, ha, ite_false, ← weightedExpectation_unused,
      availabilityTangent, W, v, μ] using h

/-- The output derivative vanishes at both singular endpoints of the arcsine metric. -/
theorem availabilityTangent_endpoint {d q : ℕ} (F : Finset (Fin q))
    (A ξ : Fin d → Fin q → ℝ) {s : ℝ} (hW : RowSurplus (maskedWeights F A) s) :
    EndpointTangent (availabilityStep F A) (availabilityTangent F A ξ hW) := by
  classical
  intro a ha
  let μ := law _ hW.nonneg (partition_pos _ hW)
  have hz (hmean : colorMean μ a = 0) : availabilityTangent F A ξ hW a = 0 := by
    unfold availabilityTangent
    rw [colorCovarianceAction_zero]
    · simp
    · intro i
      have hi : mean μ i a ≤ colorMean μ a :=
        single_le_sum (fun j _ => mean_nonneg μ j a) (mem_univ i)
      exact le_antisymm (by linarith) (mean_nonneg μ i a)
  by_cases haF : a ∈ F
  · exact hz (colorMean_eq_zero_of_column_zero _ hW.nonneg (partition_pos _ hW) a
      (fun i => by simp [maskedWeights, haF]))
  · rcases ha with ha | ha
    · have hlo := (availabilityStep_bounds F A hW a haF).1
      have hp : 0 < s / ((d : ℝ) + s) :=
        div_pos hW.positive (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hW.positive)
      exfalso
      linarith
    · apply hz
      rw [availabilityStep_eq F A hW a, ite_eq_right haF] at ha
      change 1 - colorMean μ a = 1 at ha
      linarith

/-- Output Bernoulli variance agrees exactly, including pinned colors. -/
theorem availabilityStep_variance {d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) {s : ℝ} (hW : RowSurplus (maskedWeights F A) s) (c : Fin q) :
    availabilityStep F A c * (1 - availabilityStep F A c) =
      colorMean (law _ hW.nonneg (partition_pos _ hW)) c *
        (1 - colorMean (law _ hW.nonneg (partition_pos _ hW)) c) := by
  classical
  rw [availabilityStep_eq F A hW c]
  by_cases hc : c ∈ F
  · have hz := colorMean_eq_zero_of_column_zero _ hW.nonneg (partition_pos _ hW) c
      (fun i => by simp [maskedWeights, hc])
    simp [hc, hz]
  · simp only [hc, ite_false]
    ring

private theorem cell_energy_bound {D s a p ξ : ℝ} (hD : 0 ≤ D) (hs : 0 < s)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hplus : a = 0 ∨ s / (D + s) ≤ a)
    (htan : a = 0 ∨ a = 1 → ξ = 0) (hp : p ≤ a / (s + 1)) :
    p * (ξ / a)^2 ≤ D / ((D + s) * (s + 1)) * (ξ^2 / (a * (1 - a))) := by
  by_cases he : a = 0 ∨ a = 1
  · simp [htan he]
  · have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm (fun h => he (Or.inl h)))
    have ha' : a < 1 := lt_of_le_of_ne ha1 (fun h => he (Or.inr h))
    have hb : 0 < 1 - a := by linarith
    have hds : 0 < D + s := add_pos_of_nonneg_of_pos hD hs
    have ht : 0 < s + 1 := by linarith
    have hlo : s / (D + s) ≤ a := hplus.resolve_left (fun h => he (Or.inl h))
    have hcomp : 1 - a ≤ D / (D + s) := by
      have hid : 1 - s / (D + s) = D / (D + s) := by field_simp; ring
      linarith
    have hpr : p * (1 - a) / a ≤ D / ((D + s) * (s + 1)) := by
      calc
        _ ≤ (a / (s + 1)) * (1 - a) / a :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hb.le) ha0.le
        _ = (1 - a) / (s + 1) := by field_simp
        _ ≤ (D / (D + s)) / (s + 1) := div_le_div_of_nonneg_right hcomp ht.le
        _ = _ := by field_simp
    calc
      _ = (p * (1 - a) / a) * (ξ^2 / (a * (1 - a))) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hpr (div_nonneg (sq_nonneg _) (mul_pos ha0 hb).le)

/-- Conditional on the retained-column covariance bound, the exact recursion's
Jacobian contracts the sum of all child squared arcsine norms with the paper's constant. -/
theorem availabilityTangent_square_bound {Δ d q : ℕ} (F : Finset (Fin q))
    (A ξ : Fin d → Fin q → ℝ) {s β : ℝ} (hW : RowSurplus (maskedWeights F A) s)
    (hA0 : ∀ i c, 0 ≤ A i c) (hA1 : ∀ i c, A i c ≤ 1)
    (hplus : ∀ i c, A i c = 0 ∨ s / ((Δ : ℝ) + s) ≤ A i c)
    (htan : ∀ i, EndpointTangent (A i) (ξ i)) (hβ : 0 ≤ β)
    (hcov : (β • columnBlock (law _ hW.nonneg (partition_pos _ hW)) -
      covariance (law _ hW.nonneg (partition_pos _ hW))).PosSemidef) :
    arcsineNormSq (availabilityStep F A) (availabilityTangent F A ξ hW) ≤
      β^2 * ((Δ : ℝ) / (((Δ : ℝ) + s) * (s + 1))) *
        ∑ i, arcsineNormSq (A i) (ξ i) := by
  classical
  let μ := law _ hW.nonneg (partition_pos _ hW)
  let v : Fin d × Fin q → ℝ := fun x => ξ x.1 x.2 / A x.1 x.2
  let k := (Δ : ℝ) / (((Δ : ℝ) + s) * (s + 1))
  have hp (i : Fin d) (c : Fin q) : mean μ i c ≤ A i c / (s + 1) := by
    apply (marginal_le _ hW i c).trans
    apply div_le_div_of_nonneg_right _ (by linarith [hW.positive])
    by_cases hc : c ∈ F <;> simp [maskedWeights, hc, hA0 i c]
  have hinput : (∑ x, mean μ x.1 x.2 * v x ^ 2) ≤
      k * ∑ i, arcsineNormSq (A i) (ξ i) := by
    rw [Fintype.sum_prod_type]
    simp only [arcsineNormSq, Finset.mul_sum]
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro c _
    exact cell_energy_bound (Nat.cast_nonneg Δ) hW.positive (hA0 i c) (hA1 i c)
      (hplus i c) (htan i c) (hp i c)
  have hout := colorCovarianceAction_bound μ hβ hcov v
  have hin := covariance_input_bound μ hβ hcov v
  have hid : arcsineNormSq (availabilityStep F A) (availabilityTangent F A ξ hW) =
      ∑ c, colorCovarianceAction μ v c ^ 2 / (colorMean μ c * (1 - colorMean μ c)) := by
    unfold arcsineNormSq availabilityTangent
    simp only [neg_sq, availabilityStep_variance F A hW]
    rfl
  rw [hid]
  calc
    _ ≤ β * (v ⬝ᵥ covariance μ *ᵥ v) := hout
    _ ≤ β * (β * ∑ x, mean μ x.1 x.2 * v x ^ 2) := mul_le_mul_of_nonneg_left hin hβ
    _ ≤ β * (β * (k * ∑ i, arcsineNormSq (A i) (ξ i))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinput hβ) hβ
    _ = _ := by dsimp only [k]; ring

/-- The all-child maximum estimate keeps the exact factor `d`. -/
theorem availabilityTangent_max_square_bound {Δ d q : ℕ} (F : Finset (Fin q))
    (A ξ : Fin d → Fin q → ℝ) {s β M : ℝ} (hW : RowSurplus (maskedWeights F A) s)
    (hA0 : ∀ i c, 0 ≤ A i c) (hA1 : ∀ i c, A i c ≤ 1)
    (hplus : ∀ i c, A i c = 0 ∨ s / ((Δ : ℝ) + s) ≤ A i c)
    (htan : ∀ i, EndpointTangent (A i) (ξ i)) (hβ : 0 ≤ β)
    (hcov : (β • columnBlock (law _ hW.nonneg (partition_pos _ hW)) -
      covariance (law _ hW.nonneg (partition_pos _ hW))).PosSemidef)
    (hM : ∀ i, arcsineNormSq (A i) (ξ i) ≤ M) :
    arcsineNormSq (availabilityStep F A) (availabilityTangent F A ξ hW) ≤
      β^2 * ((d : ℝ) * Δ / (((Δ : ℝ) + s) * (s + 1))) * M := by
  have hsum : (∑ i, arcsineNormSq (A i) (ξ i)) ≤ (d : ℝ) * M := by
    calc
      _ ≤ ∑ _i : Fin d, M := sum_le_sum (fun i _ => hM i)
      _ = _ := by simp
  apply (availabilityTangent_square_bound F A ξ hW hA0 hA1 hplus htan hβ hcov).trans
  calc
    _ ≤ β^2 * ((Δ : ℝ) / (((Δ : ℝ) + s) * (s + 1))) * ((d : ℝ) * M) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg _)
        (div_nonneg (Nat.cast_nonneg _) (mul_nonneg
          (add_nonneg (Nat.cast_nonneg _) hW.positive.le) (by linarith [hW.positive]))))
    _ = _ := by ring

/-- A local nonnegative coordinate has zero derivative when it is zero. -/
theorem derivative_zero_at_zero {f : ℝ → ℝ} {f' θ : ℝ}
    (hf : HasDerivAt f f' θ) (hn : ∀ᶠ t in nhds θ, 0 ≤ f t) (hz : f θ = 0) : f' = 0 := by
  apply IsLocalMin.hasDerivAt_eq_zero _ hf
  change ∀ᶠ t in nhds θ, f θ ≤ f t
  simpa only [hz] using hn

/-- The actual covariance formula has a uniform coordinate-speed bound even
before positive nonzero-message lower bounds become available. -/
theorem availabilityTangent_speed_bound {d q : ℕ} (F : Finset (Fin q))
    (A ξ : Fin d → Fin q → ℝ) {s M : ℝ} (hW : RowSurplus (maskedWeights F A) s)
    (hA0 : ∀ i c, 0 ≤ A i c) (hM : 0 ≤ M) (hspeed : ∀ i c, |ξ i c| ≤ M)
    (a : Fin q) :
    |availabilityTangent F A ξ hW a| ≤ (d : ℝ) * q / (s + 1) * M := by
  classical
  let μ := law _ hW.nonneg (partition_pos _ hW)
  let f : Injection d q → ℝ := fun σ => if a ∉ Set.range σ then 1 else 0
  let v : Fin d × Fin q → ℝ := fun x => ξ x.1 x.2 / A x.1 x.2
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have hp (i : Fin d) (c : Fin q) : mean μ i c ≤ A i c / (s + 1) := by
    apply (marginal_le _ hW i c).trans
    apply div_le_div_of_nonneg_right _ ht.le
    by_cases hc : c ∈ F <;> simp [maskedWeights, hc, hA0 i c]
  have hcell (x : Fin d × Fin q) : |μ.covariance f (cell x.1 x.2) * v x| ≤ M / (s + 1) := by
    have hc := abs_covariance_cell_le_mean μ f
      (fun σ => by dsimp only [f]; split_ifs <;> norm_num)
      (fun σ => by dsimp only [f]; split_ifs <;> norm_num) x
    rw [abs_mul]
    calc
      _ ≤ mean μ x.1 x.2 * |v x| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ ≤ (A x.1 x.2 / (s + 1)) * |v x| := mul_le_mul_of_nonneg_right (hp _ _) (abs_nonneg _)
      _ ≤ M / (s + 1) := by
        dsimp only [v]
        rw [abs_div, abs_of_nonneg (hA0 _ _)]
        by_cases hx : A x.1 x.2 = 0
        · simp [hx, div_nonneg hM ht.le]
        · have heq : A x.1 x.2 / (s + 1) * (|ξ x.1 x.2| / A x.1 x.2) =
              |ξ x.1 x.2| / (s + 1) := by field_simp
          rw [heq]
          exact div_le_div_of_nonneg_right (hspeed _ _) ht.le
  have heq : availabilityTangent F A ξ hW a = ∑ x, μ.covariance f (cell x.1 x.2) * v x := by
    rw [← covariance_injectionScore, covariance_unused_score]
    rfl
  rw [heq]
  calc
    _ ≤ ∑ x, |μ.covariance f (cell x.1 x.2) * v x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Fin d × Fin q, M / (s + 1) := sum_le_sum (fun x _ => hcell x)
    _ = _ := by simp; ring

/-- On a nonnegative differentiable path, the uniform speed estimate applies
also at coordinates that are zero. -/
theorem hasDerivAt_availabilityStep_speed {d q : ℕ} (F : Finset (Fin q))
    (A : ℝ → Fin d → Fin q → ℝ) (ξ : Fin d → Fin q → ℝ) (θ : ℝ) {s M : ℝ}
    (hW : RowSurplus (maskedWeights F (A θ)) s)
    (hderiv : ∀ i c, HasDerivAt (fun t => A t i c) (ξ i c) θ)
    (hA0 : ∀ i c, 0 ≤ A θ i c)
    (hnear : ∀ i c, ∀ᶠ t in nhds θ, 0 ≤ A t i c)
    (hM : 0 ≤ M) (hspeed : ∀ i c, |ξ i c| ≤ M) (a : Fin q) :
    HasDerivAt (fun t => availabilityStep F (A t) a)
      (availabilityTangent F (A θ) ξ hW a) θ ∧
    |availabilityTangent F (A θ) ξ hW a| ≤ (d : ℝ) * q / (s + 1) * M := by
  exact ⟨hasDerivAt_availabilityStep F A ξ θ hW hderiv
    (fun i c hz => derivative_zero_at_zero (hderiv i c) (hnear i c) hz) a,
    availabilityTangent_speed_bound F (A θ) ξ hW hA0 hM hspeed a⟩

/-- The original finite uniform speed constant in Section 6.2. -/
noncomputable def bufferSpeedConstant (Δ q : ℕ) (s : ℝ) : ℝ :=
  2 * Δ * ((q : ℝ) / (s + 1))^Δ

theorem speed_coefficient_le_bufferConstant {Δ d q : ℕ} {s : ℝ}
    (hΔ : 1 ≤ Δ) (hd : d ≤ Δ) (hs : 0 < s) (hq : s + 1 ≤ q) :
    (d : ℝ) * q / (s + 1) ≤ bufferSpeedConstant Δ q s := by
  have ht : 0 < s + 1 := by linarith
  have hbase : 1 ≤ (q : ℝ) / (s + 1) := (le_div_iff₀ ht).mpr (by simpa using hq)
  have hpower : (q : ℝ) / (s + 1) ≤ ((q : ℝ) / (s + 1))^Δ :=
    le_self_pow₀ hbase (Nat.ne_zero_of_lt hΔ)
  have hd' : (d : ℝ) ≤ Δ := by exact_mod_cast hd
  have hnonneg : 0 ≤ (Δ : ℝ) * ((q : ℝ) / (s + 1))^Δ := by positivity
  calc
    _ = (d : ℝ) * ((q : ℝ) / (s + 1)) := by ring
    _ ≤ (Δ : ℝ) * ((q : ℝ) / (s + 1)) :=
      mul_le_mul_of_nonneg_right hd' (by positivity)
    _ ≤ (Δ : ℝ) * ((q : ℝ) / (s + 1))^Δ :=
      mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg _)
    _ ≤ bufferSpeedConstant Δ q s := by unfold bufferSpeedConstant; nlinarith

/-- The speed lemma at every interior point of the closed interpolation interval.
No endpoint derivatives of the raw cut interpolation are required. -/
theorem hasDerivAt_availabilityStep_buffer_speed {Δ d q : ℕ} (F : Finset (Fin q))
    (A : ℝ → Fin d → Fin q → ℝ) (ξ : Fin d → Fin q → ℝ) (θ : ℝ) {s M : ℝ}
    (hW : RowSurplus (maskedWeights F (A θ)) s)
    (hderiv : ∀ i c, HasDerivAt (fun t => A t i c) (ξ i c) θ)
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i c, 0 ≤ A t i c)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hM : 0 ≤ M) (hspeed : ∀ i c, |ξ i c| ≤ M)
    (hΔ : 1 ≤ Δ) (hd : d ≤ Δ) (hq : s + 1 ≤ q) (a : Fin q) :
    HasDerivAt (fun t => availabilityStep F (A t) a)
      (availabilityTangent F (A θ) ξ hW a) θ ∧
    |availabilityTangent F (A θ) ξ hW a| ≤ bufferSpeedConstant Δ q s * M := by
  have hnear : ∀ i c, ∀ᶠ t in nhds θ, 0 ≤ A t i c := by
    intro i c
    filter_upwards [Icc_mem_nhds hθ.1 hθ.2] with t ht
    exact hpath t ht i c
  have h := hasDerivAt_availabilityStep_speed F A ξ θ hW hderiv
    (hpath θ ⟨hθ.1.le, hθ.2.le⟩) hnear hM hspeed a
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (speed_coefficient_le_bufferConstant hΔ hd hW.positive hq) hM

/-- The literal affine cut interpolation lies in the original convex domain. -/
theorem affine_cut_domain {Δ q : ℕ} {A B : Fin q → ℝ}
    (hA : MessageDomain Δ q A) (hB : MessageDomain Δ q B)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    MessageDomain Δ q (fun c => (1 - θ) * A c + θ * B c) :=
  hA.convex_combination hB hθ.1 hθ.2

/-- The cut interpolation has unit coordinate speed, including its endpoints. -/
theorem affine_cut_speed {Δ q : ℕ} {A B : Fin q → ℝ}
    (hA : MessageDomain Δ q A) (hB : MessageDomain Δ q B) (θ : ℝ) (c : Fin q) :
    HasDerivAt (fun t : ℝ => (1 - t) * A c + t * B c) (B c - A c) θ ∧
      |B c - A c| ≤ 1 := by
  constructor
  · convert! (((hasDerivAt_const θ (1 : ℝ)).sub (hasDerivAt_id θ)).mul_const (A c)).add
      ((hasDerivAt_id θ).mul_const (B c)) using 1; simp; ring
  · exact abs_le.mpr ⟨by linarith [hA.le_one c, hB.nonneg c],
      by linarith [hB.le_one c, hA.nonneg c]⟩

/-- Every exactly generated message belongs to the paper's strengthened domain. -/
theorem availabilityStep_generated_plus {Δ d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) {s : ℝ} (hW : RowSurplus (maskedWeights F A) s)
    (hd : d ≤ Δ) (c : Fin q) :
    availabilityStep F A c = 0 ∨ s / ((Δ : ℝ) + s) ≤ availabilityStep F A c := by
  classical
  by_cases hc : c ∈ F
  · exact Or.inl (by simp [availabilityStep, hc])
  · exact Or.inr (availabilityStep_uniform_lower F A hW hd c hc)

/-- The original energy bound above the two-level buffer. -/
noncomputable def bufferEnergyConstant (Δ q : ℕ) (s : ℝ) : ℝ :=
  Real.sqrt q * (bufferSpeedConstant Δ q s)^2 /
    Real.sqrt ((s / ((Δ : ℝ) + s)) *
      (s * (s + 1) / ((q : ℝ) * ((Δ : ℝ) + s)^2)))

/-- Two genuine recursion levels turn any unit-speed interpolation of cut
messages in the original domain into the uniformly bounded arcsine speed `E₀`.
All derivatives and all surplus certificates belong to this same interpolation. -/
theorem two_level_buffer {Δ d q : ℕ} (F : Finset (Fin q))
    (n : Fin d → ℕ) (Fchild : Fin d → Finset (Fin q))
    (B : ℝ → (i : Fin d) → Fin (n i) → Fin q → ℝ)
    (ξ : (i : Fin d) → Fin (n i) → Fin q → ℝ) (θ : ℝ)
    (hΔ : 2 ≤ Δ) (hs : 0 < (q : ℝ) - 2 * Δ + 2)
    (hdegree : F.card + d + 1 ≤ Δ)
    (hchilddegree : ∀ i, (Fchild i).card + n i + 1 ≤ Δ)
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j, MessageDomain Δ q (B t i j))
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hderiv : ∀ i j c, HasDerivAt (fun t => B t i j c) (ξ i j c) θ)
    (hspeed : ∀ i j c, |ξ i j c| ≤ 1) :
    ∃ η : Fin q → ℝ,
      (∀ c, HasDerivAt
        (fun t => availabilityStep F (fun i => availabilityStep (Fchild i) (B t i)) c)
        (η c) θ) ∧
      EndpointTangent
        (availabilityStep F (fun i => availabilityStep (Fchild i) (B θ i))) η ∧
      arcsineNorm (availabilityStep F (fun i => availabilityStep (Fchild i) (B θ i))) η ≤
        bufferEnergyConstant Δ q ((q : ℝ) - 2 * Δ + 2) := by
  classical
  let s : ℝ := (q : ℝ) - 2 * Δ + 2
  let K := bufferSpeedConstant Δ q s
  let A := fun t i => availabilityStep (Fchild i) (B t i)
  have hs' : 0 < s := hs
  have hΔ' : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hq : s + 1 ≤ q := by dsimp [s]; linarith
  have hqpos : 0 < (q : ℝ) := by dsimp [s] at hs'; linarith
  have hd : d ≤ Δ := by omega
  have hn (i : Fin d) : n i ≤ Δ := by have h := hchilddegree i; omega
  have ht : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨hθ.1.le, hθ.2.le⟩
  have hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, MessageDomain Δ q (A t i) := by
    intro t ht' i
    exact availabilityStep_mem_domain (Fchild i) (B t i) (hpath t ht' i) (hchilddegree i) hs
  let hWi := fun i => maskedWeights_rowSurplus (Fchild i) (B θ i)
    (hpath θ ht i) (hchilddegree i) hs
  let χ := fun i => availabilityTangent (Fchild i) (B θ i) (ξ i) (hWi i)
  have hχ (i : Fin d) (c : Fin q) :
      HasDerivAt (fun t => A t i c) (χ i c) θ ∧ |χ i c| ≤ K := by
    have h := hasDerivAt_availabilityStep_buffer_speed (Fchild i) (fun t => B t i)
      (ξ i) θ (hWi i) (hderiv i)
      (fun t ht' j c => (hpath t ht' i j).nonneg c) hθ
      (by norm_num : (0 : ℝ) ≤ 1) (hspeed i) (by omega : 1 ≤ Δ) (hn i) hq c
    simpa only [mul_one] using h
  have hK : 0 ≤ K := by unfold K bufferSpeedConstant; positivity
  let hW := maskedWeights_rowSurplus F (A θ) (hA θ ht) hdegree hs
  let η := availabilityTangent F (A θ) χ hW
  have hη (c : Fin q) : HasDerivAt (fun t => availabilityStep F (A t) c) (η c) θ ∧
      |η c| ≤ K^2 := by
    have h := hasDerivAt_availabilityStep_buffer_speed F A χ θ hW
      (fun i c => (hχ i c).1) (fun t ht' i c => (hA t ht' i).nonneg c)
      hθ hK (fun i c => (hχ i c).2) (by omega : 1 ≤ Δ) hd hq c
    simpa only [K, pow_two] using h
  have hend : EndpointTangent (availabilityStep F (A θ)) η :=
    availabilityTangent_endpoint F (A θ) χ hW
  refine ⟨η, fun c => (hη c).1, hend, ?_⟩
  let I : Finset (Fin q) := univ.filter (fun c => c ∉ F ∧ ∃ i, c ∉ Fchild i)
  let a := s / ((Δ : ℝ) + s)
  let b := s * (s + 1) / ((q : ℝ) * ((Δ : ℝ) + s)^2)
  have ha : 0 < a := div_pos hs' (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hs')
  have hb : 0 < b := by dsimp only [b]; positivity
  have hbuf (c : Fin q) := availabilityStep_buffer F Fchild (A θ) hW hd
    (fun i c hc => by simp [A, availabilityStep, hc])
    (fun i c hc => availabilityStep_uniform_lower (Fchild i) (B θ i) (hWi i) (hn i) c hc) c
  have hlo : ∀ c ∈ I, a ≤ availabilityStep F (A θ) c := by
    intro c hc
    have hc' : c ∉ F ∧ ∃ i, c ∉ Fchild i := by simpa [I] using hc
    exact ((hbuf c).2.2 hc'.1 hc'.2).1
  have hhi : ∀ c ∈ I, availabilityStep F (A θ) c ≤ 1 - b := by
    intro c hc
    have hc' : c ∉ F ∧ ∃ i, c ∉ Fchild i := by simpa [I] using hc
    exact ((hbuf c).2.2 hc'.1 hc'.2).2
  have hzero : ∀ c ∉ I, η c = 0 := by
    intro c hc
    apply hend c
    by_cases hcF : c ∈ F
    · exact Or.inl ((hbuf c).1 hcF)
    · apply Or.inr
      apply (hbuf c).2.1 hcF
      intro i
      by_contra hi
      exact hc (by simp [I, hcF, show ∃ i, c ∉ Fchild i from ⟨i, hi⟩])
  exact arcsineNorm.buffer_bound ha hb (sq_nonneg K) hlo hhi hzero (fun c => (hη c).2)

/-- The paper's unsquared one-step contraction, ready for recursive path speeds. -/
theorem availabilityTangent_contraction {Δ d q : ℕ} (F : Finset (Fin q))
    (A ξ : Fin d → Fin q → ℝ) {s β κ M : ℝ} (hW : RowSurplus (maskedWeights F A) s)
    (hA0 : ∀ i c, 0 ≤ A i c) (hA1 : ∀ i c, A i c ≤ 1)
    (hplus : ∀ i c, A i c = 0 ∨ s / ((Δ : ℝ) + s) ≤ A i c)
    (htan : ∀ i, EndpointTangent (A i) (ξ i)) (hβ : 0 ≤ β)
    (hcov : (β • columnBlock (law _ hW.nonneg (partition_pos _ hW)) -
      covariance (law _ hW.nonneg (partition_pos _ hW))).PosSemidef)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hparam : β^2 * ((d : ℝ) * Δ / (((Δ : ℝ) + s) * (s + 1))) ≤ κ^2)
    (hspeed : ∀ i, arcsineNorm (A i) (ξ i) ≤ M) :
    arcsineNorm (availabilityStep F A) (availabilityTangent F A ξ hW) ≤ κ * M := by
  have hspeedSq (i : Fin d) : arcsineNormSq (A i) (ξ i) ≤ M^2 := by
    rw [← arcsineNorm.sq (hA0 i) (hA1 i)]
    nlinarith [hspeed i, arcsineNorm.nonneg (A := A i) (ξ := ξ i)]
  have hbound := availabilityTangent_max_square_bound F A ξ hW hA0 hA1 hplus htan hβ hcov hspeedSq
  unfold arcsineNorm
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hκ hM, ?_⟩
  apply hbound.trans
  calc
    _ ≤ κ^2 * M^2 := mul_le_mul_of_nonneg_right hparam (sq_nonneg M)
    _ = _ := by ring

end EdgeColoringMixing
