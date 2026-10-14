import MainTheorems.WishartBlocks.DampedDifferentialUniqueness
import MainTheorems.WishartBlocks.MatrixEuclidean

namespace ResearchMain.WishartBlocks

open MeasureTheory Matrix
open scoped BigOperators FourierTransform InnerProductSpace Matrix.Norms.Elementwise SchwartzMap

noncomputable def matrixLaplaceListSymbol {p : ℕ} (T : Matrix (Fin p) (Fin p) ℝ)
    (L : List (Matrix (Fin p) (Fin p) ℝ)) : ℂ :=
  match L with
  | [] => 1
  | H :: L => (-((T * H).trace : ℂ)) * matrixLaplaceListSymbol T L

theorem matrix_directionLaplacePolynomial {p : ℕ} (ξ : MatrixEuclidean p)
    (L : List (Matrix (Fin p) (Fin p) ℝ)) (hL : ∀ H ∈ L, H.IsHermitian) (t : ℝ) :
    (directionLaplacePolynomial (coordinateTrace p) (L.map (matrixCoordinates p)) ξ).eval (t : ℂ) =
      matrixLaplaceListSymbol (1 + t • matrixFrequency ξ) L := by
  induction L with
  | nil => simp [directionLaplacePolynomial, matrixLaplaceListSymbol]
  | cons H L ih =>
      have hH := hL H (List.mem_cons_self ..)
      have hTail : ∀ J ∈ L, J.IsHermitian := fun J hJ => hL J (List.mem_cons_of_mem H hJ)
      simp only [List.map_cons, directionLaplacePolynomial, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
        coordinateTrace_matrixCoordinates, ih hTail, matrixLaplaceListSymbol]
      congr 1
      rw [identity_shift_trace, matrixFrequency_trace ξ hH]
      push_cast
      ring

theorem matrix_weightedLaplace_composition {X : Type*} [MeasurableSpace X] {p : ℕ}
    (μ : Measure X) (W : X → Matrix (Fin p) (Fin p) ℝ)
    (hW : ∀ᵐ x ∂μ, (W x).PosSemidef) (ξ : MatrixEuclidean p) (c : X → ℂ) (t : ℝ) :
    weightedLaplace μ (fun x => coordinateTrace p (matrixCoordinates p (W x)))
      (fun x => -2 * Real.pi * inner ℝ ξ (matrixCoordinates p (W x))) c t =
      ∫ x, c x * (Real.exp (-((1 + t • matrixFrequency ξ) * W x).trace) : ℂ) ∂μ := by
  unfold weightedLaplace
  apply integral_congr_ae
  filter_upwards [hW] with x hx
  rw [coordinateTrace_matrixCoordinates, ← matrixFrequency_trace ξ hx.1]
  have he : -((W x).trace : ℂ) - (t : ℂ) *
      ((matrixFrequency ξ * W x).trace : ℂ) =
      (-((1 + t • matrixFrequency ξ) * W x).trace : ℝ) := by
    rw [identity_shift_trace]
    push_cast
    ring
  rw [he, ← Complex.ofReal_exp]

theorem matrix_direction_coefficient_integrable {X : Type*} [MeasurableSpace X]
    {p : ℕ} (μ : Measure X) (W : X → Matrix (Fin p) (Fin p) ℝ) (hWm : Measurable W)
    (hW : ∀ᵐ x ∂μ, (W x).PosSemidef) (ξ : MatrixEuclidean p)
    (c : X → ℂ) (hc : Measurable c)
    (hi : Integrable (fun x => ‖W x‖ * ‖c x‖) μ) :
    Integrable (fun x => |-2 * Real.pi * inner ℝ ξ (matrixCoordinates p (W x))| * ‖c x‖) μ := by
  let C := (p : ℝ) ^ 3 * ‖matrixFrequency ξ‖
  have hin : Measurable (fun x => inner ℝ ξ (matrixCoordinates p (W x))) :=
    (measurable_const : Measurable (fun _ : X => ξ)).inner
      ((matrixCoordinates p).continuous.measurable.comp hWm)
  have hm : Measurable (fun x => |-2 * Real.pi * inner ℝ ξ (matrixCoordinates p (W x))| *
      ‖c x‖) := (continuous_abs.measurable.comp
        (hin.const_mul (-2 * Real.pi))).fun_mul hc.norm
  apply (hi.const_mul C).mono' hm.aestronglyMeasurable
  filter_upwards [hW] with x hx
  rw [← matrixFrequency_trace ξ hx.1]
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
  have htrace : (W x).trace ≤ (p : ℝ) * ‖W x‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.trace_nonneg] using matrix_trace_norm_bound (W x)
  have hb := trace_direction_bound_on_positive (matrixFrequency ξ) hx
  have hbound : |(matrixFrequency ξ * W x).trace| ≤ C * ‖W x‖ := by
    calc
      _ ≤ ((p : ℝ) ^ 2 * ‖matrixFrequency ξ‖) * (W x).trace := hb
      _ ≤ ((p : ℝ) ^ 2 * ‖matrixFrequency ξ‖) * ((p : ℝ) * ‖W x‖) :=
        mul_le_mul_of_nonneg_left htrace (by positivity)
      _ = C * ‖W x‖ := by dsimp [C]; ring
  calc
    _ ≤ (C * ‖W x‖) * ‖c x‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ = C * (‖W x‖ * ‖c x‖) := by ring

theorem matrix_laplace_differential_unique {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] {p : ℕ} (μ : Measure X) [SFinite μ]
    (W : X → Matrix (Fin p) (Fin p) ℝ) (hWm : Measurable W)
    (hW : ∀ᵐ x ∂μ, (W x).PosSemidef)
    (c : ι → X → ℂ) (hc : ∀ i, Measurable (c i)) (hi : ∀ i, Integrable (c i) μ)
    (hci : ∀ i, Integrable (fun x => ‖W x‖ * ‖c i x‖) μ)
    (L : ι → List (Matrix (Fin p) (Fin p) ℝ))
    (hL : ∀ i H, H ∈ L i → H.IsHermitian)
    (hzero : ∀ T : Matrix (Fin p) (Fin p) ℝ, T.PosSemidef →
      (∑ i, matrixLaplaceListSymbol T (L i) *
        ∫ x, c i x * (Real.exp (-(T * W x).trace) : ℂ) ∂μ) = 0)
    (f : 𝓢(MatrixEuclidean p, ℂ)) :
    (∑ i, ∫ x, c i x * functionDirections ((L i).map (matrixCoordinates p))
      (fun y => exponentialDamping (coordinateTrace p) y * f y)
        (matrixCoordinates p (W x)) ∂μ) = 0 := by
  apply laplace_differential_unique μ (fun x => matrixCoordinates p (W x))
    ((matrixCoordinates p).continuous.measurable.comp hWm) (coordinateTrace p)
    c hc hi (fun i => (L i).map (matrixCoordinates p))
    (fun ξ => matrixStripRadius (matrixFrequency ξ))
    (fun ξ => matrixStripRadius_pos (matrixFrequency ξ))
  · intro ξ
    filter_upwards [hW] with x hx
    rw [coordinateTrace_matrixCoordinates, ← matrixFrequency_trace ξ hx.1]
    exact matrixStripRadius_trace_damping (matrixFrequency ξ) hx
  · intro ξ i
    exact matrix_direction_coefficient_integrable μ W hWm hW ξ (c i) (hc i) (hci i)
  · intro ξ t ht
    simp_rw [matrix_directionLaplacePolynomial ξ _ (hL _),
      matrix_weightedLaplace_composition μ W hW]
    exact hzero _ (identity_shift_positive (matrixFrequency_isHermitian ξ) ht)

end ResearchMain.WishartBlocks
