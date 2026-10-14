import ChowlaCosine.ConvolutionFourier
import ChowlaCosine.WeightedRoth

/-! The actual convolution selector and its quantitative estimates. -/
namespace ChowlaCosine

open MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate

/-- Coefficients extended by zero off the given finite support. -/
noncomputable def supportedCoefficient (A : Finset ℤ) (s : ℤ → ℝ) (m : ℤ) : ℝ :=
  if m ∈ A then s m else 0

/-- The real Fourier coefficient of the perturbed selector. -/
noncomputable def selectorCoefficient (A : Finset ℤ) (s : ℤ → ℝ) (t m : ℤ) : ℝ :=
  supportedCoefficient A s m * supportedCoefficient A s (m-t) *
    (1 - supportedCoefficient A s (m+t))

/-- Multiplication by the character of frequency `t`. -/
noncomputable def modulate (t : ℤ) (f : Circle → ℂ) (x : Circle) : ℂ :=
  fourier t x * f x

/-- The selector in Lemma 4.1, defined using the actual circle convolution. -/
noncomputable def selector (A : Finset ℤ) (s : ℤ → ℝ) (t : ℤ) : Circle → ℂ :=
  convolve (polynomial A s) (modulate t (polynomial A s)) -
    convolve (convolve (polynomial A s) (modulate t (polynomial A s)))
      (modulate (-t) (polynomial A s))

/-- Continuity of convolution on the compact circle. -/
theorem continuous_convolve {f g : Circle → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (convolve f g) := by
  exact (HasCompactSupport.of_compactSpace g).continuous_convolution_right
    (ContinuousLinearMap.mul ℂ ℂ) hf.locallyIntegrable hg

/-- Continuous functions with finite real Fourier coefficients equal their finite polynomial. -/
theorem eq_polynomial_of_fourierCoeff {f : Circle → ℂ} (hf : Continuous f)
    (A : Finset ℤ) (s : ℤ → ℝ)
    (hcoeff : ∀ m, fourierCoeff f m = if m ∈ A then (s m : ℂ) else 0) :
    f = polynomial A s := by
  let fc : C(Circle, ℂ) := ⟨f, hf⟩
  have hzero : ∀ m ∉ A, fourierCoeff fc m = 0 := by
    intro m hm
    exact (hcoeff m).trans (ite_eq_right hm)
  have hsum : Summable (fourierCoeff fc) := summable_of_ne_finset_zero hzero
  funext x
  have hpoint := has_pointwise_sum_fourier_series_of_summable hsum x
  have hfin : HasSum (fun m => fourierCoeff fc m • fourier m x)
      (∑ m ∈ A, fourierCoeff fc m • fourier m x) :=
    hasSum_sum_of_ne_finset_zero (fun m hm => by rw [hzero m hm, zero_smul])
  have heq := hpoint.unique hfin
  change f x = _ at heq
  rw [heq, polynomial_apply]
  apply Finset.sum_congr rfl
  intro m hm
  change fourierCoeff f m * fourier m x = _
  rw [hcoeff, ite_eq_left hm]

@[simp] theorem selectorCoefficient_zero_outside {A : Finset ℤ} (s : ℤ → ℝ) (t : ℤ)
    {m : ℤ} (hm : m ∉ A) : selectorCoefficient A s t m = 0 := by
  simp [selectorCoefficient, supportedCoefficient, hm]

/-- The coefficient vanishes away from the two support pieces. -/
theorem selectorCoefficient_zero_off_BC (A : Finset ℤ) (s : ℤ → ℝ) (t m : ℤ)
    (hm : m ∉ B A t ∪ C A t) : selectorCoefficient A s t m = 0 := by
  by_cases hmA : m ∈ A
  · by_cases hmt : m-t ∈ A
    · exfalso
      apply hm
      by_cases hp : m+t ∈ A <;> simp [B, C, hmA, hmt, hp]
    · simp [selectorCoefficient, supportedCoefficient, hmt]
  · exact selectorCoefficient_zero_outside s t hmA

/-- On `B_t`, the selector coefficient lies between the squared endpoint coefficients. -/
theorem selectorCoefficient_mem_B {A : Finset ℤ} {s : ℤ → ℝ} {t m : ℤ}
    (hs : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01) (hm : m ∈ B A t) :
    selectorCoefficient A s t m ∈ Set.Icc ((0.99 : ℝ)^2) ((1.01 : ℝ)^2) := by
  obtain ⟨hmA, hmt, hp⟩ := Finset.mem_filter.mp hm
  have hsm := hs m hmA
  have hst := hs (m-t) hmt
  simp only [selectorCoefficient, supportedCoefficient, ite_eq_left hmA, ite_eq_left hmt,
    ite_eq_right hp, sub_zero, mul_one]
  constructor
  · have hh := mul_le_mul hsm.1 hst.1 (by norm_num : (0:ℝ) ≤ 0.99)
      (by linarith [hsm.1] : 0 ≤ s m)
    nlinarith only [hh]
  · have hh := mul_le_mul hsm.2 hst.2 (by linarith [hst.1] : 0 ≤ s (m-t))
      (by norm_num : (0:ℝ) ≤ 1.01)
    nlinarith only [hh]

/-- On `C_t`, the perturbation error is at most `β²/100`. -/
theorem abs_selectorCoefficient_mem_C {A : Finset ℤ} {s : ℤ → ℝ} {t m : ℤ}
    (hs : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01) (hm : m ∈ C A t) :
    |selectorCoefficient A s t m| ≤ (1.01 : ℝ)^2/100 := by
  obtain ⟨hmA, hmt, hp⟩ := Finset.mem_filter.mp hm
  have hsm := hs m hmA
  have hst := hs (m-t) hmt
  have hsp := hs (m+t) hp
  have hsm0 : 0 ≤ s m := by linarith [hsm.1]
  have hst0 : 0 ≤ s (m-t) := by linarith [hst.1]
  have hprod : s m * s (m-t) ≤ (1.01 : ℝ)^2 := by
    have hh := mul_le_mul hsm.2 hst.2 hst0 (by norm_num : (0:ℝ) ≤ 1.01)
    nlinarith only [hh]
  have herr : |1-s (m+t)| ≤ (1/100 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [hsp.1, hsp.2]
  simp only [selectorCoefficient, supportedCoefficient, ite_eq_left hmA, ite_eq_left hmt,
    ite_eq_left hp, abs_mul, abs_of_nonneg hsm0, abs_of_nonneg hst0]
  have hh := mul_le_mul hprod herr (abs_nonneg _) (sq_nonneg (1.01 : ℝ))
  nlinarith only [hh]

/-- The two selector pieces are disjoint subsets of the original support. -/
theorem selector_BC_disjoint (A : Finset ℤ) (t : ℤ) : Disjoint (B A t) (C A t) := by
  apply Finset.disjoint_left.mpr
  intro m hb hc
  exact (Finset.mem_filter.mp hb).2.2 (Finset.mem_filter.mp hc).2.2

/-- The sum of the squared selector coefficients has the release's two-piece bound. -/
theorem selectorCoefficient_sum_sq_le {A : Finset ℤ} {s : ℤ → ℝ} (t : ℤ)
    (hs : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01) :
    (∑ m ∈ A, selectorCoefficient A s t m ^ 2) ≤
      (1.01 : ℝ)^4 * (B A t).card + ((1.01 : ℝ)^2/100)^2 * (C A t).card := by
  have hsub : B A t ∪ C A t ⊆ A := by
    intro m hm
    rcases Finset.mem_union.mp hm with hb | hc
    · exact (Finset.mem_filter.mp hb).1
    · exact (Finset.mem_filter.mp hc).1
  have heq := Finset.sum_subset (f := fun m => selectorCoefficient A s t m ^ 2) hsub
    (fun m hm hnot => by rw [selectorCoefficient_zero_off_BC A s t m hnot]; simp)
  rw [← heq, Finset.sum_union (selector_BC_disjoint A t)]
  have hB : (∑ m ∈ B A t, selectorCoefficient A s t m ^ 2) ≤
      (1.01 : ℝ)^4 * (B A t).card := by
    calc
      _ ≤ ∑ m ∈ B A t, (1.01 : ℝ)^4 := by
        apply Finset.sum_le_sum
        intro m hm
        have hb := selectorCoefficient_mem_B hs hm
        have hnonneg : 0 ≤ selectorCoefficient A s t m := by linarith [hb.1]
        have hsq := (sq_le_sq₀ hnonneg (sq_nonneg (1.01 : ℝ))).2 hb.2
        nlinarith only [hsq]
      _ = _ := by simp [mul_comm]
  have hC : (∑ m ∈ C A t, selectorCoefficient A s t m ^ 2) ≤
      ((1.01 : ℝ)^2/100)^2 * (C A t).card := by
    calc
      _ ≤ ∑ m ∈ C A t, ((1.01 : ℝ)^2/100)^2 := by
        apply Finset.sum_le_sum
        intro m hm
        have hc := abs_selectorCoefficient_mem_C hs hm
        have hsq := (sq_le_sq₀ (abs_nonneg (selectorCoefficient A s t m))
          (by positivity : 0 ≤ (1.01 : ℝ)^2/100)).2 hc
        simpa only [sq_abs] using hsq
      _ = _ := by simp [mul_comm]
  exact add_le_add hB hC

theorem continuous_modulate (t : ℤ) {f : Circle → ℂ} (hf : Continuous f) :
    Continuous (modulate t f) := (fourier t).continuous.mul hf

@[simp] theorem norm_modulate (t : ℤ) (f : Circle → ℂ) (x : Circle) :
    ‖modulate t f x‖ = ‖f x‖ := by
  simp [modulate, fourier_apply, Circle.norm_coe]

theorem fourierCoeff_modulate (t : ℤ) (f : Circle → ℂ) (m : ℤ) :
    fourierCoeff (modulate t f) m = fourierCoeff f (m-t) := by
  rw [show modulate t f = (fun x => f x * fourier t x) by funext x; exact mul_comm _ _]
  exact fourierCoeff_mul_character f t m

theorem continuous_selector (A : Finset ℤ) (s : ℤ → ℝ) (t : ℤ) :
    Continuous (selector A s t) := by
  have hF := (polynomial A s).continuous
  have hH := continuous_convolve hF (continuous_modulate t hF)
  exact hH.sub (continuous_convolve hH (continuous_modulate (-t) hF))

theorem fourierCoeff_sub {f g : Circle → ℂ}
    (hf : Integrable f haarAddCircle) (hg : Integrable g haarAddCircle) (m : ℤ) :
    fourierCoeff (f-g) m = fourierCoeff f m - fourierCoeff g m := by
  simp only [fourierCoeff, Pi.sub_apply, smul_sub]
  exact integral_sub (hf.fourier_smul _) (hg.fourier_smul _)

/-- Young's inequality gives the raw selector bound without assumptions on the coefficients. -/
theorem selector_integral_norm_raw (A : Finset ℤ) (s : ℤ → ℝ) (t : ℤ) :
    (∫ x, ‖selector A s t x‖ ∂haarAddCircle) ≤
      (∫ x, ‖polynomial A s x‖ ∂haarAddCircle)^2 +
      (∫ x, ‖polynomial A s x‖ ∂haarAddCircle)^3 := by
  let F : Circle → ℂ := polynomial A s
  let H := convolve F (modulate t F)
  let J := convolve H (modulate (-t) F)
  let N := ∫ x, ‖F x‖ ∂haarAddCircle
  have hF : Integrable F haarAddCircle :=
    (polynomial A s).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp : Integrable (modulate t F) haarAddCircle := hF.fourier_smul t
  have hn : Integrable (modulate (-t) F) haarAddCircle := hF.fourier_smul (-t)
  have hH : Integrable H haarAddCircle := integrable_convolve hF hp
  have hJ : Integrable J haarAddCircle := integrable_convolve hH hn
  have hN : 0 ≤ N := integral_nonneg (fun _ => norm_nonneg _)
  have hbH : (∫ x, ‖H x‖ ∂haarAddCircle) ≤ N^2 := by
    have hh := integral_norm_convolve_le hF hp
    simpa only [norm_modulate, pow_two] using hh
  have hbJ : (∫ x, ‖J x‖ ∂haarAddCircle) ≤ N^3 := by
    have hh := integral_norm_convolve_le hH hn
    simp only [norm_modulate] at hh
    have hmul := mul_le_mul_of_nonneg_right hbH hN
    calc
      _ ≤ (∫ x, ‖H x‖ ∂haarAddCircle) * N := hh
      _ ≤ N^2*N := hmul
      _ = N^3 := by ring
  calc
    _ ≤ ∫ x, (‖H x‖ + ‖J x‖) ∂haarAddCircle := by
      apply integral_mono (hH.sub hJ).norm (hH.norm.add hJ.norm)
      intro x
      exact norm_sub_le (H x) (J x)
    _ = (∫ x, ‖H x‖ ∂haarAddCircle) + (∫ x, ‖J x‖ ∂haarAddCircle) :=
      integral_add hH.norm hJ.norm
    _ ≤ N^2+N^3 := add_le_add hbH hbJ

/-- Lemma 4.1's uniform L¹ bound for the actual selector. -/
theorem selector_integral_norm_le {A : Finset ℤ} {s : ℤ → ℝ} {K : ℝ} (t : ℤ)
    (hne : A.Nonempty) (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hcoeff : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01)
    (hlower : ∀ x, -K ≤ (polynomial A s x).re) :
    (∫ x, ‖selector A s t x‖ ∂haarAddCircle) ≤ 13*K^3 := by
  obtain ⟨a, ha⟩ := hne
  have hKbound := polynomial_coefficient_le h0 hA hs hlower ha
  have hK : (0.99 : ℝ) ≤ K := by
    have ha0 := (hcoeff a ha).1
    have has := le_abs_self (s a)
    linarith
  have hK0 : 0 ≤ K := by linarith
  let N := ∫ x, ‖polynomial A s x‖ ∂haarAddCircle
  have hN0 : 0 ≤ N := integral_nonneg (fun _ => norm_nonneg _)
  have hN : N ≤ 2*K := polynomial_integral_norm_le h0 hA hs hlower
  have h2 := pow_le_pow_left₀ hN0 hN 2
  have h3 := pow_le_pow_left₀ hN0 hN 3
  have hraw := selector_integral_norm_raw A s t
  change (∫ x, ‖selector A s t x‖ ∂haarAddCircle) ≤ N^2+N^3 at hraw
  have hK2 : 0 ≤ K^2 := sq_nonneg K
  have hmargin := mul_nonneg (show 0 ≤ 5*K-4 by linarith) hK2
  nlinarith only [hraw, h2, h3, hmargin]

/-- Fourier coefficients of the actual convolution selector. -/
theorem fourierCoeff_selector (A : Finset ℤ) (s : ℤ → ℝ) (t m : ℤ) :
    fourierCoeff (selector A s t) m = (selectorCoefficient A s t m : ℂ) := by
  have hF := (polynomial A s).continuous
  have hp := continuous_modulate t hF
  have hn := continuous_modulate (-t) hF
  have hH := continuous_convolve hF hp
  have hiH : Integrable (convolve (polynomial A s) (modulate t (polynomial A s)))
      haarAddCircle :=
    hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiJ : Integrable
      (convolve (convolve (polynomial A s) (modulate t (polynomial A s)))
        (modulate (-t) (polynomial A s))) haarAddCircle :=
    (continuous_convolve hH hn).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold selector
  rw [fourierCoeff_sub hiH hiJ,
    fourierCoeff_convolve hF hp, fourierCoeff_convolve hH hn,
    fourierCoeff_convolve hF hp]
  simp only [fourierCoeff_modulate, polynomial_fourierCoeff, sub_neg_eq_add]
  unfold selectorCoefficient supportedCoefficient
  push_cast
  split_ifs <;> (try simp only [Complex.ofReal_zero]) <;> ring

/-- The selector is an actual finite Fourier polynomial with the calculated real coefficients. -/
theorem selector_eq_polynomial (A : Finset ℤ) (s : ℤ → ℝ) (t : ℤ) :
    selector A s t = polynomial A (selectorCoefficient A s t) := by
  apply eq_polynomial_of_fourierCoeff (continuous_selector A s t)
  intro m
  rw [fourierCoeff_selector]
  by_cases hm : m ∈ A
  · simp [hm]
  · simp [hm]

/-- Exact finite Parseval identity for the actual selector. -/
theorem selector_integral_norm_sq (A : Finset ℤ) (s : ℤ → ℝ) (t : ℤ) :
    (∫ x, ‖selector A s t x‖^2 ∂haarAddCircle) =
      ∑ m ∈ A, selectorCoefficient A s t m ^ 2 := by
  rw [selector_eq_polynomial]
  exact integral_norm_sq_polynomial A (selectorCoefficient A s t)

/-- Lemma 4.1's L² estimate for the actual selector. -/
theorem selector_integral_norm_sq_le {A : Finset ℤ} {s : ℤ → ℝ} (t : ℤ)
    (hs : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01) :
    (∫ x, ‖selector A s t x‖^2 ∂haarAddCircle) ≤
      (1.01 : ℝ)^4 * (B A t).card + ((1.01 : ℝ)^2/100)^2 * (C A t).card := by
  rw [selector_integral_norm_sq]
  exact selectorCoefficient_sum_sq_le t hs

/-- A real-coefficient finite Fourier polynomial has conjugate symmetry in its argument. -/
theorem polynomial_neg_argument (A : Finset ℤ) (s : ℤ → ℝ) (x : Circle) :
    polynomial A s (-x) = conj (polynomial A s x) := by
  simp only [polynomial_apply, map_sum, map_mul, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  simp only [fourier_apply, zsmul_neg, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

/-- The selector's absolute value is even, as needed for the final test function. -/
theorem selector_neg_argument (A : Finset ℤ) (s : ℤ → ℝ) (t : ℤ) (x : Circle) :
    selector A s t (-x) = conj (selector A s t x) := by
  rw [selector_eq_polynomial]
  exact polynomial_neg_argument A (selectorCoefficient A s t) x

theorem norm_selector_neg (A : Finset ℤ) (s : ℤ → ℝ) (t : ℤ) (x : Circle) :
    ‖selector A s t (-x)‖ = ‖selector A s t x‖ := by
  rw [selector_neg_argument]
  exact Complex.norm_conj _

end ChowlaCosine
