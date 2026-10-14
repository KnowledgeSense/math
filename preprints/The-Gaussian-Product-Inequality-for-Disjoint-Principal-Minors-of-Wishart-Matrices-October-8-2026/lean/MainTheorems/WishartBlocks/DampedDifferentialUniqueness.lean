import MainTheorems.WishartBlocks.DifferentialFourierUniqueness
import MainTheorems.WishartBlocks.LaplaceStripContinuation
import Mathlib.Analysis.Complex.RealDeriv

namespace ResearchMain.WishartBlocks

open MeasureTheory FourierTransform LineDeriv
open scoped BigOperators FourierTransform InnerProductSpace SchwartzMap

noncomputable def dampedSchwartzDirections {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (τ : E →L[ℝ] ℝ) (L : List E) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  match L with
  | [] => f
  | u :: L => ∂_{u} (dampedSchwartzDirections τ L f) -
      (τ u : ℂ) • dampedSchwartzDirections τ L f

noncomputable def dampedFourierSymbol {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (τ : E →L[ℝ] ℝ) (L : List E) (ξ : E) : ℂ :=
  match L with
  | [] => 1
  | u :: L => (-(τ u : ℂ) + (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ ξ u : ℂ)) *
      dampedFourierSymbol τ L ξ

noncomputable def directionLaplacePolynomial {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (τ : E →L[ℝ] ℝ) (L : List E) (ξ : E) : Polynomial ℂ :=
  match L with
  | [] => 1
  | u :: L => (Polynomial.C (-(τ u : ℂ)) +
      Polynomial.C (2 * (Real.pi : ℂ) * (inner ℝ ξ u : ℂ)) * Polynomial.X) *
        directionLaplacePolynomial τ L ξ

theorem directionLaplacePolynomial_eval_I {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (τ : E →L[ℝ] ℝ) (L : List E) (ξ : E) :
    (directionLaplacePolynomial τ L ξ).eval Complex.I = dampedFourierSymbol τ L ξ := by
  induction L with
  | nil => simp [directionLaplacePolynomial, dampedFourierSymbol]
  | cons u L ih =>
      simp only [directionLaplacePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_X, ih, dampedFourierSymbol]
      congr 1
      ring

theorem fourier_dampedSchwartzDirections {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (τ : E →L[ℝ] ℝ) (L : List E) (f : 𝓢(E, ℂ)) (ξ : E) :
    (𝓕 (dampedSchwartzDirections τ L f)) ξ = dampedFourierSymbol τ L ξ * (𝓕 f) ξ := by
  induction L with
  | nil => simp [dampedSchwartzDirections, dampedFourierSymbol]
  | cons u L ih =>
      rw [dampedSchwartzDirections, sub_eq_add_neg, FourierTransform.fourier_add,
        FourierTransform.fourier_neg, FourierTransform.fourier_smul,
        SchwartzMap.fourier_lineDerivOp_eq]
      have hg : (inner ℝ · u).HasTemperateGrowth := by fun_prop
      simp only [add_apply, neg_apply, smul_apply,
        SchwartzMap.smulLeftCLM_apply_apply hg, Complex.real_smul, smul_eq_mul, ih,
        dampedFourierSymbol]
      ring

noncomputable def exponentialDamping {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (τ : E →L[ℝ] ℝ) (x : E) : ℂ :=
  Complex.exp (-(τ x : ℂ))

theorem exponentialDamping_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (τ : E →L[ℝ] ℝ) (x : E) (hx : 0 ≤ τ x) :
    ‖exponentialDamping τ x‖ ≤ 1 := by
  rw [exponentialDamping, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)

theorem damped_first_lineDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : E →L[ℝ] ℝ) (u x : E) (f : 𝓢(E, ℂ)) :
    lineDeriv ℝ (fun y => exponentialDamping τ y * f y) x u =
      exponentialDamping τ x * (∂_{u} f - (τ u : ℂ) • f) x := by
  have he := (((Complex.ofRealCLM.comp τ).hasFDerivAt (x := x)).neg.cexp).mul
    (f.differentiableAt (x := x)).hasFDerivAt
  change HasFDerivAt (fun y => exponentialDamping τ y * f y) _ x at he
  rw [he.differentiableAt.lineDeriv_eq_fderiv, he.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, neg_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    sub_apply, exponentialDamping, Pi.neg_apply]
  ring

noncomputable def functionDirections {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : List E) (f : E → ℂ) : E → ℂ :=
  match L with
  | [] => f
  | u :: L => fun x => lineDeriv ℝ (functionDirections L f) x u

theorem functionDirections_damped {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : E →L[ℝ] ℝ) (L : List E) (f : 𝓢(E, ℂ)) (x : E) :
    functionDirections L (fun y => exponentialDamping τ y * f y) x =
      exponentialDamping τ x * dampedSchwartzDirections τ L f x := by
  induction L generalizing x with
  | nil => rfl
  | cons u L ih =>
      change lineDeriv ℝ (functionDirections L _) x u = _
      have he : functionDirections L (fun y => exponentialDamping τ y * f y) =
          fun y => exponentialDamping τ y * dampedSchwartzDirections τ L f y := by
        funext y
        exact ih y
      rw [he, damped_first_lineDeriv]
      rfl

theorem damped_differential_fourier_unique {X E ι : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (μ : Measure X) [SFinite μ] (m : X → E) (hm : Measurable m)
    (τ : E →L[ℝ] ℝ) (c : ι → X → ℂ) (hc : ∀ i, Measurable (c i))
    (hi : ∀ i, Integrable (c i) μ) (L : ι → List E)
    (hzero : ∀ ξ : E, (∑ i, dampedFourierSymbol τ (L i) ξ *
      ∫ x, c i x * inverseFourierKernel ξ (m x) ∂μ) = 0)
    (f : 𝓢(E, ℂ)) :
    (∑ i, ∫ x, c i x * dampedSchwartzDirections τ (L i) f (m x) ∂μ) = 0 := by
  have hb (i : ι) := weighted_fourierInv_integral μ m hm (c i) (hc i) (hi i)
    (𝓕 (dampedSchwartzDirections τ (L i) f))
  have hi' (i : ι) : Integrable (fun ξ =>
      (𝓕 (dampedSchwartzDirections τ (L i) f)) ξ *
        ∫ x, c i x * inverseFourierKernel ξ (m x) ∂μ) := (hb i).1
  have he (i : ι) : (∫ x, c i x * dampedSchwartzDirections τ (L i) f (m x) ∂μ) =
      ∫ ξ, (𝓕 (dampedSchwartzDirections τ (L i) f)) ξ *
        ∫ x, c i x * inverseFourierKernel ξ (m x) ∂μ := by
    simpa only [fourierInv_fourier_eq] using (hb i).2
  simp_rw [he]
  rw [← integral_finsetSum (s := Finset.univ) (fun i _ => hi' i)]
  apply integral_eq_zero_of_ae
  exact ae_of_all _ fun ξ => by
    simp_rw [fourier_dampedSchwartzDirections]
    calc
      _ = (𝓕 f) ξ * ∑ i, dampedFourierSymbol τ (L i) ξ *
          ∫ x, c i x * inverseFourierKernel ξ (m x) ∂μ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hzero ξ, mul_zero]

theorem laplace_differential_unique {X E ι : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (μ : Measure X) [SFinite μ] (m : X → E) (hm : Measurable m)
    (τ : E →L[ℝ] ℝ) (c : ι → X → ℂ) (hc : ∀ i, Measurable (c i))
    (hi : ∀ i, Integrable (c i) μ) (L : ι → List E)
    (δ : E → ℝ) (hδ : ∀ ξ, 0 < δ ξ)
    (hab : ∀ ξ, ∀ᵐ x ∂μ, δ ξ * |-2 * Real.pi * inner ℝ ξ (m x)| ≤ τ (m x))
    (hbi : ∀ ξ i, Integrable
      (fun x => |-2 * Real.pi * inner ℝ ξ (m x)| * ‖c i x‖) μ)
    (hreal : ∀ ξ t, |t| < δ ξ → (∑ i,
      (directionLaplacePolynomial τ (L i) ξ).eval (t : ℂ) *
        weightedLaplace μ (fun x => τ (m x))
          (fun x => -2 * Real.pi * inner ℝ ξ (m x)) (c i) t) = 0)
    (f : 𝓢(E, ℂ)) :
    (∑ i, ∫ x, c i x *
      functionDirections (L i) (fun y => exponentialDamping τ y * f y) (m x) ∂μ) = 0 := by
  let d := fun i x => c i x * exponentialDamping τ (m x)
  have hd (i : ι) : Measurable (d i) := by dsimp [d, exponentialDamping]; fun_prop
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ τ (m x) := by
    filter_upwards [hab (0 : E)] with x hx
    simpa only [inner_zero_left, mul_zero, abs_zero] using hx
  have hdi (i : ι) : Integrable (d i) μ := by
    apply (hi i).norm.mono' (hd i).aestronglyMeasurable
    filter_upwards [hnonneg] with x hx
    dsimp [d]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (exponentialDamping_norm τ (m x) hx)
      (norm_nonneg _)).trans_eq (mul_one _)
  have hzero : ∀ ξ : E, (∑ i, dampedFourierSymbol τ (L i) ξ *
      ∫ x, d i x * inverseFourierKernel ξ (m x) ∂μ) = 0 := by
    intro ξ
    have h := polynomial_weightedLaplace_imaginary_zero
      (by fun_prop) (by fun_prop) c (fun i => directionLaplacePolynomial τ (L i) ξ)
      hc hi (hbi ξ) (hδ ξ) (hab ξ) (hreal ξ) 1
    have he (i : ι) : weightedLaplace μ (fun x => τ (m x))
        (fun x => -2 * Real.pi * inner ℝ ξ (m x)) (c i) Complex.I =
        ∫ x, d i x * inverseFourierKernel ξ (m x) ∂μ := by
      unfold weightedLaplace
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change c i x * Complex.exp (-(τ (m x) : ℂ) - Complex.I *
          (-2 * Real.pi * inner ℝ ξ (m x) : ℝ)) =
          d i x * inverseFourierKernel ξ (m x)
        have hex : -(τ (m x) : ℂ) - Complex.I *
            (-2 * Real.pi * inner ℝ ξ (m x) : ℝ) =
            -(τ (m x) : ℂ) + (2 * Real.pi * inner ℝ ξ (m x) : ℝ) * Complex.I := by
          push_cast
          ring
        rw [hex, Complex.exp_add]
        simp only [d, exponentialDamping, inverseFourierKernel, mul_assoc]
    simpa only [Complex.ofReal_one, mul_one, directionLaplacePolynomial_eval_I, he] using h
  have h := damped_differential_fourier_unique μ m hm τ d hd hdi L hzero f
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change c i x * functionDirections (L i)
      (fun y => exponentialDamping τ y * f y) (m x) =
      d i x * dampedSchwartzDirections τ (L i) f (m x)
    rw [functionDirections_damped]
    simp only [d, mul_assoc]

end ResearchMain.WishartBlocks
