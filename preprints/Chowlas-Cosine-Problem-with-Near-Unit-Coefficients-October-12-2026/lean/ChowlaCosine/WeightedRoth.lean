import ChowlaCosine.BasicEstimates
import ChowlaCosine.FiniteParseval
import ChowlaCosine.Counting
import Mathlib.Algebra.QuadraticDiscriminant

/-! The weighted Roth argument for the original circle integral. -/
namespace ChowlaCosine

open MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate

private theorem circle_integrable {f : Circle → ℝ} (hf : Continuous f) :
    Integrable f haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Weighted Cauchy--Schwarz, proved by integrating a nonnegative square. -/
theorem weighted_cauchy_schwarz {P E : Circle → ℝ}
    (hP : Continuous P) (hE : Continuous E) (hP0 : ∀ x, 0 ≤ P x) :
    (∫ x, P x * E x ∂haarAddCircle) ^ 2 ≤
      (∫ x, P x ∂haarAddCircle) * (∫ x, P x * E x ^ 2 ∂haarAddCircle) := by
  have hiP := circle_integrable hP
  have hiPE : Integrable (fun x => P x * E x) haarAddCircle :=
    circle_integrable (hP.mul hE)
  have hiPE2 : Integrable (fun x => P x * E x^2) haarAddCircle :=
    circle_integrable (hP.mul (hE.pow 2))
  have hquad : ∀ c : ℝ, 0 ≤
      (∫ x, P x ∂haarAddCircle) * (c * c) +
      (2 * ∫ x, P x * E x ∂haarAddCircle) * c +
      (∫ x, P x * E x ^ 2 ∂haarAddCircle) := by
    intro c
    have hn : 0 ≤ ∫ x, P x * (E x + c)^2 ∂haarAddCircle :=
      integral_nonneg (fun x => mul_nonneg (hP0 x) (sq_nonneg _))
    have heq : (fun x => P x * (E x + c)^2) =
        (fun x => c^2 * P x + (2*c) * (P x * E x) + P x * E x^2) := by
      funext x
      ring
    have hadd := integral_add ((hiP.const_mul (c^2)).add (hiPE.const_mul (2*c))) hiPE2
    simp only [Pi.add_apply] at hadd
    rw [heq, hadd, integral_add (hiP.const_mul (c^2)) (hiPE.const_mul (2*c)),
      integral_const_mul, integral_const_mul] at hn
    nlinarith only [hn]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

/-- Multiplication by a character shifts the actual Fourier coefficient. -/
theorem fourierCoeff_mul_character (f : Circle → ℂ) (a m : ℤ) :
    fourierCoeff (fun x => f x * fourier a x) m = fourierCoeff f (m-a) := by
  unfold fourierCoeff
  congr 1
  funext x
  simp only [smul_eq_mul]
  rw [show -(m-a) = -m+a by omega, fourier_add]
  ring

/-- Finite multiplication by the unweighted support polynomial. -/
theorem fourierCoeff_mul_unit_polynomial {f : Circle → ℂ}
    (hf : Integrable f haarAddCircle) (A : Finset ℤ) (m : ℤ) :
    fourierCoeff (fun x => f x * polynomial A (fun _ => 1) x) m =
      ∑ a ∈ A, fourierCoeff f (m-a) := by
  classical
  have heq : (fun x => f x * polynomial A (fun _ => 1) x) =
      ∑ a ∈ A, (fun x => f x * fourier a x) := by
    funext x
    simp [polynomial_apply, Finset.mul_sum]
  rw [heq, fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff_mul_character]
  · intro a ha
    simpa only [smul_eq_mul, mul_comm] using hf.fourier_smul a

/-- The second moment is an actual finite Fourier pairing. -/
theorem integral_mul_unit_polynomial_sq {f : Circle → ℂ}
    (hf : Continuous f) (A : Finset ℤ) :
    (∫ x, f x * polynomial A (fun _ => 1) x *
      conj (polynomial A (fun _ => 1) x) ∂haarAddCircle) =
      ∑ t ∈ A, ∑ m ∈ A, fourierCoeff f (m-t) := by
  have hfi : Integrable f haarAddCircle := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun x => f x * polynomial A (fun _ => 1) x) haarAddCircle :=
    (hf.mul (polynomial A (fun _ => 1)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_mul_conj_polynomial hi]
  simp only [Complex.ofReal_one, one_mul, fourierCoeff_mul_unit_polynomial hfi]
  exact Finset.sum_comm

private theorem polynomial_eq_real (A : Finset ℤ) (s : ℤ → ℝ)
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a) (x : Circle) :
    polynomial A s x = ((polynomial A s x).re : ℂ) := by
  apply Complex.ext <;> simp [polynomial_im A s hA hs x]

/-- Fourier coefficients after adding the constant lower bound. -/
theorem fourierCoeff_polynomial_add_const (A : Finset ℤ) (s : ℤ → ℝ) (K : ℝ) (m : ℤ) :
    fourierCoeff (fun x => polynomial A s x + (K : ℂ)) m =
      (if m ∈ A then (s m : ℂ) else 0) + (if m = 0 then (K : ℂ) else 0) := by
  have hi : Integrable (polynomial A s) haarAddCircle :=
    (polynomial A s).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := congrFun (fourierCoeff.add hi (integrable_const (K : ℂ))) m
  change fourierCoeff (fun x : Circle => polynomial A s x + (K : ℂ)) m =
    fourierCoeff (polynomial A s) m + fourierCoeff (fun _ : Circle => (K : ℂ)) m at h
  simpa only [polynomial_fourierCoeff, fourierCoeff_const] using h

/-- The first weighted moment is the sum of the coefficients. -/
theorem roth_first_moment {A : Finset ℤ} {s : ℤ → ℝ} (K : ℝ)
    (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a) :
    (∫ x, ((polynomial A s x).re + K) *
      (polynomial A (fun _ => 1) x).re ∂haarAddCircle) = ∑ a ∈ A, s a := by
  have hi : Integrable (fun x => polynomial A s x + (K : ℂ)) haarAddCircle :=
    ((polynomial A s).continuous.add continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_mul_conj_polynomial hi A (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at h
  have hrhs : (∑ a ∈ A, fourierCoeff (fun x => polynomial A s x + (K : ℂ)) a) =
      ((∑ a ∈ A, s a : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have ha0 : a ≠ 0 := fun heq => h0 (heq ▸ ha)
    simp [fourierCoeff_polynomial_add_const, ha, ha0]
  have heq : (fun x => (polynomial A s x + (K : ℂ)) *
        conj (polynomial A (fun _ => 1) x)) =
      (fun x => ((((polynomial A s x).re + K) *
        (polynomial A (fun _ => 1) x).re : ℝ) : ℂ)) := by
    funext x
    rw [polynomial_eq_real A s hA hs x,
      polynomial_eq_real A (fun _ => 1) hA (by simp) x]
    simp
  rw [hrhs, heq, integral_complex_ofReal] at h
  exact_mod_cast h

/-- The second moment counts the actual additive triples of the support. -/
theorem roth_second_moment {A : Finset ℤ} {s : ℤ → ℝ} (K : ℝ)
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a) :
    (∫ x, ((polynomial A s x).re + K) *
      (polynomial A (fun _ => 1) x).re ^ 2 ∂haarAddCircle) =
      K * A.card + ∑ t ∈ A, ∑ m ∈ A, if m-t ∈ A then s (m-t) else 0 := by
  have h := integral_mul_unit_polynomial_sq
    (f := fun x => polynomial A s x + (K : ℂ))
    ((polynomial A s).continuous.add (continuous_const (y := (K : ℂ)))) A
  have hrhs : (∑ t ∈ A, ∑ m ∈ A,
      fourierCoeff (fun x => polynomial A s x + (K : ℂ)) (m-t)) =
      ((K * A.card + ∑ t ∈ A, ∑ m ∈ A, if m-t ∈ A then s (m-t) else 0 : ℝ) : ℂ) := by
    simp only [fourierCoeff_polynomial_add_const, Finset.sum_add_distrib]
    have hc : (∑ t ∈ A, ∑ m ∈ A, if m-t = 0 then (K : ℂ) else 0) =
        (K : ℂ) * A.card := by
      simp [sub_eq_zero, mul_comm]
    rw [hc]
    push_cast
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro m hm
    split_ifs <;> rfl
  have heq : (fun x => (polynomial A s x + (K : ℂ)) *
        polynomial A (fun _ => 1) x * conj (polynomial A (fun _ => 1) x)) =
      (fun x => ((((polynomial A s x).re + K) *
        (polynomial A (fun _ => 1) x).re ^ 2 : ℝ) : ℂ)) := by
    funext x
    rw [polynomial_eq_real A s hA hs x,
      polynomial_eq_real A (fun _ => 1) hA (by simp) x]
    simp [pow_two, mul_assoc]
  rw [hrhs, heq, integral_complex_ofReal] at h
  exact_mod_cast h

/-- The nonnegative weight has mean exactly `K`. -/
theorem roth_weight_mean {A : Finset ℤ} (s : ℤ → ℝ) (K : ℝ) (h0 : 0 ∉ A) :
    (∫ x, (polynomial A s x).re + K ∂haarAddCircle) = K := by
  have hi : Integrable (polynomial A s) haarAddCircle :=
    (polynomial A s).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ x, RCLike.re (polynomial A s x) + K ∂haarAddCircle) = K
  rw [integral_add hi.re (integrable_const K), integral_re hi, polynomial_integral A s h0]
  simp

/-- The weighted count is bounded by the coefficient upper bound times `T_A`. -/
theorem weighted_triple_sum_le {A : Finset ℤ} {s : ℤ → ℝ} {β : ℝ}
    (hβ : ∀ a ∈ A, s a ≤ β) :
    (∑ t ∈ A, ∑ m ∈ A, if m-t ∈ A then s (m-t) else 0) ≤ β * (T A : ℝ) := by
  unfold T
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  by_cases hmt : m-t ∈ A
  · simp only [hmt, ite_true, mul_one]
    exact hβ (m-t) hmt
  · simp [hmt]

/-- Roth's weighted Cauchy--Schwarz inequality with the release constants. -/
theorem polynomial_roth_inequality {A : Finset ℤ} {s : ℤ → ℝ} {K : ℝ}
    (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hcoeff : ∀ a ∈ A, s a ∈ Set.Icc (99/100 : ℝ) (101/100))
    (hlower : ∀ x, -K ≤ (polynomial A s x).re) :
    (99/100 : ℝ)^2 * (A.card : ℝ)^2 ≤
      K^2 * A.card + (101/100 : ℝ) * K * (T A : ℝ) := by
  have hP : Continuous (fun x : Circle => (polynomial A s x).re + K) :=
    (Complex.continuous_re.comp (polynomial A s).continuous).add continuous_const
  have hP0 : ∀ x : Circle, 0 ≤ (polynomial A s x).re + K := by
    intro x
    linarith [hlower x]
  have hK : 0 ≤ K := by
    rw [← roth_weight_mean s K h0]
    exact integral_nonneg hP0
  have hcs := weighted_cauchy_schwarz
    (P := fun x : Circle => (polynomial A s x).re + K)
    (E := fun x : Circle => (polynomial A (fun _ => 1) x).re)
    hP (Complex.continuous_re.comp (polynomial A (fun _ => 1)).continuous) hP0
  rw [roth_first_moment K h0 hA hs, roth_weight_mean s K h0,
    roth_second_moment K hA hs] at hcs
  have hsum : (99/100 : ℝ) * A.card ≤ ∑ a ∈ A, s a := by
    have h := Finset.sum_le_sum (s := A) (f := fun _ => (99/100 : ℝ))
      (g := s) (fun a ha => (hcoeff a ha).1)
    simpa [mul_comm] using h
  have hsum0 : 0 ≤ ∑ a ∈ A, s a := le_trans (by positivity) hsum
  have hsq : ((99/100 : ℝ) * A.card)^2 ≤ (∑ a ∈ A, s a)^2 :=
    (sq_le_sq₀ (by positivity) hsum0).2 hsum
  have hcount := weighted_triple_sum_le (fun a ha => (hcoeff a ha).2)
  have hmul := mul_le_mul_of_nonneg_left hcount hK
  nlinarith only [hsq, hcs, hmul]

/-- Lemma 2.2 of the release, for the actual finite support and circle polynomial. -/
theorem roth_counting_lower_bound {A : Finset ℤ} {s : ℤ → ℝ} {K : ℝ}
    (hne : A.Nonempty) (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hcoeff : ∀ a ∈ A, s a ∈ Set.Icc (99/100 : ℝ) (101/100))
    (hlower : ∀ x, -K ≤ (polynomial A s x).re)
    (hlarge : 3 * K^2 ≤ (A.card : ℝ)) :
    (A.card : ℝ)^2 / (2*K) ≤ (T A : ℝ) := by
  obtain ⟨a, ha⟩ := hne
  have hKbound := polynomial_coefficient_le h0 hA hs hlower ha
  have hK : 0 < K := by
    have ha0 := (hcoeff a ha).1
    have has := le_abs_self (s a)
    linarith
  have hR := polynomial_roth_inequality h0 hA hs hcoeff hlower
  have hn : 0 ≤ (A.card : ℝ) := by positivity
  have hsmall := mul_le_mul_of_nonneg_right hlarge hn
  apply (div_le_iff₀ (by positivity : 0 < 2*K)).2
  nlinarith [sq_nonneg (A.card : ℝ)]

/-- Combining Roth with the genuine support-counting lemma gives the bound on `Btot`. -/
theorem roth_Btot_lower_bound {A : Finset ℤ} {s : ℤ → ℝ} {K : ℝ}
    (hne : A.Nonempty) (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hcoeff : ∀ a ∈ A, s a ∈ Set.Icc (99/100 : ℝ) (101/100))
    (hlower : ∀ x, -K ≤ (polynomial A s x).re)
    (hlarge : 3 * K^2 ≤ (A.card : ℝ)) :
    (A.card : ℝ)^2 / (6*K) ≤ (Btot A : ℝ) := by
  have hR := roth_counting_lower_bound hne h0 hA hs hcoeff hlower hlarge
  have hB : (T A : ℝ) ≤ 3 * (Btot A : ℝ) := by
    exact_mod_cast shankar_counting (fun a ha => (hA a).2 ha) h0
  obtain ⟨a, ha⟩ := hne
  have hKbound := polynomial_coefficient_le h0 hA hs hlower ha
  have hK : 0 < K := by
    have ha0 := (hcoeff a ha).1
    have has := le_abs_self (s a)
    linarith
  have hR' := (div_le_iff₀ (by positivity : 0 < 2*K)).mp hR
  apply (div_le_iff₀ (by positivity : 0 < 6*K)).2
  nlinarith

end ChowlaCosine
