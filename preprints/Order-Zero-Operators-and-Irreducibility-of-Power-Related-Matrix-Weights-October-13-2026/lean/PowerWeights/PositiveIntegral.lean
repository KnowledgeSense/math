import PowerWeights.MeasureModel

namespace PowerWeights

open MeasureTheory Matrix
open scoped ComplexOrder

 theorem complex_integral_pos {μ : Measure ℝ} (hμ : μ≠0) (f : ℝ → ℂ)
    (hf : Integrable f μ) (hp : ∀ᵐ x ∂μ, 0<f x) : 0<∫ x, f x ∂μ := by
  have hpr : ∀ᵐ x ∂μ, 0<RCLike.re (f x) := hp.mono fun _ h => (RCLike.pos_iff.mp h).1
  have hpi : ∀ᵐ x ∂μ, RCLike.im (f x)=0 := hp.mono fun _ h => (RCLike.pos_iff.mp h).2
  have hs : Function.support (fun x => RCLike.re (f x)) =ᵐ[μ] Set.univ := by
    filter_upwards [hpr] with x hx
    change 0<(f x).re at hx
    simp [Function.mem_support,hx.ne']
  have hpos : 0<∫ x, RCLike.re (f x) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg_ae (hpr.mono fun _ h => h.le) hf.re).mpr
    rw [measure_congr hs]
    exact Measure.measure_univ_pos.mpr hμ
  apply RCLike.pos_iff.mpr
  constructor
  · rwa [integral_re hf] at hpos
  · rw [← integral_im hf,integral_congr_ae hpi]
    simp

 theorem integral_matrix_posDef_of_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure ℝ} (hμ : μ≠0)
    (W : ℝ → Matrix ι ι ℂ)
    (hi : ∀ i j, Integrable (fun x => W x i j) μ)
    (hH : ∀ᵐ x ∂μ, (W x).IsHermitian)
    (hQ : ∀ v : ι → ℂ, v≠0 → ∀ᵐ x ∂μ, 0<star v ⬝ᵥ (W x *ᵥ v)) :
    Matrix.PosDef (fun i j => ∫ x, W x i j ∂μ) := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.ext
    intro i j
    change (starRingEnd ℂ) (∫ x, W x j i ∂μ)=∫ x, W x i j ∂μ
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    exact congrArg (fun M : Matrix ι ι ℂ => M i j) hx
  · intro v hv
    let f : ℝ → ℂ := fun x => star v ⬝ᵥ (W x *ᵥ v)
    have hfi : Integrable f μ := by
      dsimp [f]
      simp only [dotProduct,mulVec,Finset.mul_sum]
      apply integrable_finsetSum
      intro i _
      apply integrable_finsetSum
      intro j _
      exact ((hi i j).mul_const (v j)).const_mul (star (v i))
    have hfp : ∀ᵐ x ∂μ, 0<f x := hQ v hv
    have hz := complex_integral_pos hμ f hfi hfp
    have he : ∫ x, f x ∂μ = star v ⬝ᵥ
        ((fun i j => ∫ x, W x i j ∂μ : Matrix ι ι ℂ) *ᵥ v) := by
      dsimp [f]
      simp only [dotProduct,mulVec,Finset.mul_sum]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        · simp only [integral_const_mul,integral_mul_const]
        · intro j _
          exact ((hi i j).mul_const (v j)).const_mul (star (v i))
      · intro i _
        apply integrable_finsetSum
        intro j _
        exact ((hi i j).mul_const (v j)).const_mul (star (v i))
    rwa [he] at hz

 theorem integral_matrix_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure ℝ} (hμ : μ≠0) (W : ℝ → Matrix ι ι ℂ)
    (hi : ∀ i j, Integrable (fun x => W x i j) μ)
    (hp : ∀ᵐ x ∂μ, (W x).PosDef) :
    Matrix.PosDef (fun i j => ∫ x, W x i j ∂μ) :=
  integral_matrix_posDef_of_quadratic hμ W hi (hp.mono fun _ hx => hx.isHermitian)
    (fun _v hv => hp.mono fun _ hx => hx.dotProduct_mulVec_pos hv)

end PowerWeights
