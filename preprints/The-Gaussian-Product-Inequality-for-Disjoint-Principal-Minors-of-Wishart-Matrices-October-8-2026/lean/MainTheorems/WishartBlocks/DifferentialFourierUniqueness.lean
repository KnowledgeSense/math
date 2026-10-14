import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open MeasureTheory FourierTransform LineDeriv
open scoped BigOperators FourierTransform InnerProductSpace SchwartzMap

noncomputable def schwartzDirections {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : List E) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  match L with
  | [] => f
  | u :: L => ∂_{u} (schwartzDirections L f)

noncomputable def fourierListSymbol {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (L : List E) (ξ : E) : ℂ :=
  match L with
  | [] => 1
  | u :: L => (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ ξ u : ℂ) * fourierListSymbol L ξ

theorem fourier_schwartzDirections {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : List E) (f : 𝓢(E, ℂ)) (ξ : E) :
    (𝓕 (schwartzDirections L f)) ξ = fourierListSymbol L ξ * (𝓕 f) ξ := by
  induction L with
  | nil => simp [schwartzDirections, fourierListSymbol]
  | cons u L ih =>
      rw [schwartzDirections, SchwartzMap.fourier_lineDerivOp_eq]
      have hg : (inner ℝ · u).HasTemperateGrowth := by fun_prop
      simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
        Complex.real_smul, smul_eq_mul, ih, fourierListSymbol]
      ring

noncomputable def inverseFourierKernel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ξ x : E) : ℂ :=
  Complex.exp ((2 * Real.pi * inner ℝ ξ x : ℝ) * Complex.I)

theorem inverseFourierKernel_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ξ x : E) : ‖inverseFourierKernel ξ x‖ = 1 := by
  unfold inverseFourierKernel
  rw [Complex.norm_exp]
  simp

theorem weighted_fourierInv_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure X) [SFinite μ]
    (m : X → E) (hm : Measurable m) (c : X → ℂ) (hc : Measurable c)
    (hi : Integrable c μ) (f : 𝓢(E, ℂ)) :
    Integrable (fun ξ => f ξ * ∫ x, c x * inverseFourierKernel ξ (m x) ∂μ) ∧
      (∫ x, c x * (𝓕⁻ f) (m x) ∂μ) =
        ∫ ξ, f ξ * ∫ x, c x * inverseFourierKernel ξ (m x) ∂μ := by
  let K := fun z : X × E => c z.1 * inverseFourierKernel z.2 (m z.1) * f z.2
  have hK : Integrable K (μ.prod volume) := by
    have hKm : AEStronglyMeasurable K (μ.prod volume) := by
      have hf : Measurable (f : E → ℂ) := f.continuous.measurable
      have hin : Measurable (fun z : X × E => inner ℝ z.2 (m z.1)) :=
        measurable_snd.inner (hm.comp measurable_fst)
      have hk : Measurable (fun z : X × E => inverseFourierKernel z.2 (m z.1)) := by
        unfold inverseFourierKernel
        exact Complex.measurable_exp.comp
          ((Complex.measurable_ofReal.comp (hin.const_mul (2 * Real.pi))).mul_const Complex.I)
      exact (((hc.comp measurable_fst).fun_mul hk).fun_mul
        (hf.comp measurable_snd)).aestronglyMeasurable
    apply (hi.norm.mul_prod f.integrable.norm).mono' hKm
    exact ae_of_all _ fun z => by
      dsimp [K]
      simp only [norm_mul, inverseFourierKernel_norm, mul_one]
      exact le_rfl
  have hleft (x : X) : c x * (𝓕⁻ f) (m x) = ∫ ξ, K (x, ξ) := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun ξ => by
      simp only [K, inverseFourierKernel, smul_eq_mul, mul_assoc]
  have hright (ξ : E) : (∫ x, K (x, ξ) ∂μ) =
      f ξ * ∫ x, c x * inverseFourierKernel ξ (m x) ∂μ := by
    dsimp [K]
    rw [integral_mul_const, mul_comm]
  constructor
  · exact hK.integral_prod_right.congr (ae_of_all _ hright)
  · calc
      _ = ∫ x, (∫ ξ, K (x, ξ)) ∂μ := integral_congr_ae (ae_of_all _ hleft)
      _ = ∫ ξ, ∫ x, K (x, ξ) ∂μ := integral_integral_swap hK
      _ = _ := integral_congr_ae (ae_of_all _ hright)

theorem differential_fourier_unique {X E ι : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (μ : Measure X) [SFinite μ] (m : X → E) (hm : Measurable m)
    (c : ι → X → ℂ) (hc : ∀ i, Measurable (c i)) (hi : ∀ i, Integrable (c i) μ)
    (L : ι → List E)
    (hzero : ∀ ξ : E, (∑ i, fourierListSymbol (L i) ξ *
      ∫ x, c i x * inverseFourierKernel ξ (m x) ∂μ) = 0)
    (f : 𝓢(E, ℂ)) :
    (∑ i, ∫ x, c i x * (schwartzDirections (L i) f) (m x) ∂μ) = 0 := by
  have hb (i : ι) := weighted_fourierInv_integral μ m hm (c i) (hc i) (hi i)
    (𝓕 (schwartzDirections (L i) f))
  have hi' (i : ι) : Integrable (fun ξ =>
      (𝓕 (schwartzDirections (L i) f)) ξ *
        ∫ x, c i x * inverseFourierKernel ξ (m x) ∂μ) := (hb i).1
  have he (i : ι) : (∫ x, c i x * (schwartzDirections (L i) f) (m x) ∂μ) =
      ∫ ξ, (𝓕 (schwartzDirections (L i) f)) ξ *
        ∫ x, c i x * inverseFourierKernel ξ (m x) ∂μ := by
    simpa only [fourierInv_fourier_eq] using (hb i).2
  simp_rw [he]
  rw [← integral_finsetSum (s := Finset.univ) (fun i _ => hi' i)]
  apply integral_eq_zero_of_ae
  exact ae_of_all _ fun ξ => by
    simp_rw [fourier_schwartzDirections]
    calc
      _ = (𝓕 f) ξ * ∑ i, fourierListSymbol (L i) ξ *
          ∫ x, c i x * inverseFourierKernel ξ (m x) ∂μ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hzero ξ, mul_zero]

end ResearchMain.WishartBlocks
