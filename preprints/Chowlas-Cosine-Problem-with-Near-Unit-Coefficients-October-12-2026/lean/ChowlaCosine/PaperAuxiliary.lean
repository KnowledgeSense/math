import ChowlaCosine.AuxiliaryFourier
import ChowlaCosine.Selector

namespace ChowlaCosine
open MeasureTheory AddCircle
open scoped ComplexConjugate

noncomputable def realPolynomial (A : Finset ℤ) (s : ℤ → ℝ) (x : Circle) : ℝ :=
  (polynomial A s x).re

noncomputable def localVector (A : Finset ℤ) (s : ℤ → ℝ) (t m : ℤ) : Fin 5 → ℝ :=
  ![supportedCoefficient A s (m-2*t), supportedCoefficient A s (m-t),
    supportedCoefficient A s m, supportedCoefficient A s (m+t), supportedCoefficient A s (m+2*t)]

theorem continuous_realPolynomial (A : Finset ℤ) (s : ℤ → ℝ) :
    Continuous (realPolynomial A s) := Complex.continuous_re.comp (polynomial A s).continuous

theorem complex_realPolynomial {A : Finset ℤ} {s : ℤ → ℝ}
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a) (x : Circle) :
    (realPolynomial A s x : ℂ) = polynomial A s x := by
  apply Complex.ext <;> simp [realPolynomial, polynomial_im A s hA hs x]

theorem paper_auxiliaryF_coeff {A : Finset ℤ} {s : ℤ → ℝ}
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a) (t m : ℤ) :
    fourierCoeff (fun x => (auxiliaryF (realPolynomial A s) t x : ℂ)) m =
      lambda (supportedCoefficient A s (m-t)) (supportedCoefficient A s m)
        (supportedCoefficient A s (m+t)) := by
  rw [fourierCoeff_auxiliaryF (continuous_realPolynomial A s)]
  simp_rw [complex_realPolynomial hA hs, polynomial_fourierCoeff]
  simp only [lambda, supportedCoefficient, Complex.ofReal_sub, apply_ite Complex.ofReal,
    Complex.ofReal_zero]
  ring

theorem paper_auxiliaryR_coeff {A : Finset ℤ} {s : ℤ → ℝ}
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a) (t m : ℤ) :
    fourierCoeff (fun x => (auxiliaryR (realPolynomial A s) t x : ℂ)) m =
      rho (localVector A s t m) := by
  rw [fourierCoeff_auxiliaryR (continuous_realPolynomial A s)]
  simp_rw [paper_auxiliaryF_coeff hA hs]
  simp only [rho, localVector, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  rw [show m-t-t=m-2*t by ring, show m-t+t=m by ring,
    show m+t-t=m by ring, show m+t+t=m+2*t by ring]
  rfl

theorem continuous_auxiliaryR {F : Circle → ℝ} (hF : Continuous F) (t : ℤ) :
    Continuous (auxiliaryR F t) := by
  have hf := Complex.continuous_ofReal.comp (continuous_auxiliaryF hF t)
  have hc := continuous_convolve hf hf
  have he : (fun x => (convolve (fun y => (auxiliaryF F t y : ℂ))
      (fun y => (auxiliaryF F t y : ℂ)) x).re) =
      realConvolve (auxiliaryF F t) (auxiliaryF F t) := by
    ext x
    rw [← complex_realConvolve]
    rfl
  have hr : Continuous (realConvolve (auxiliaryF F t) (auxiliaryF F t)) := by
    rw [← he]; exact Complex.continuous_re.comp hc
  unfold auxiliaryR phaseCosine
  exact (continuous_const.sub
    (Complex.continuous_re.comp (continuous_const.mul (fourier t).continuous))).mul hr

theorem paper_auxiliaryPsi_coeff {A : Finset ℤ} {s : ℤ → ℝ}
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a) (t m : ℤ) :
    fourierCoeff (fun x => (auxiliaryPsi (realPolynomial A s) t x : ℂ)) m =
      (R (localVector A s t m) : ℂ) := by
  unfold auxiliaryPsi
  rw [fourierCoeff_evenPart (continuous_auxiliaryR (continuous_realPolynomial A s) t),
    paper_auxiliaryR_coeff hA hs, rho_re]

theorem paper_auxiliaryPhi_coeff {A : Finset ℤ} {s : ℤ → ℝ}
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a) (t m : ℤ) :
    fourierCoeff (fun x => (auxiliaryPhi (realPolynomial A s) t x : ℂ)) m =
      -Complex.I * (J (localVector A s t m) : ℂ) := by
  unfold auxiliaryPhi
  rw [fourierCoeff_oddPart (continuous_auxiliaryR (continuous_realPolynomial A s) t),
    paper_auxiliaryR_coeff hA hs, ← rho_neg_im]
  push_cast
  ring

def auxiliarySpectrum (A : Finset ℤ) (t : ℤ) : Finset ℤ :=
  A.biUnion (fun a => {a-2*t, a-t, a, a+t, a+2*t})

theorem localVector_zero_off_spectrum {A : Finset ℤ} {s : ℤ → ℝ} {t m : ℤ}
    (hm : m ∉ auxiliarySpectrum A t) : localVector A s t m = 0 := by
  have hz (a : ℤ) (ha : m ∈ ({a-2*t, a-t, a, a+t, a+2*t} : Finset ℤ)) :
      supportedCoefficient A s a = 0 := by
    have hn : a ∉ A := by
      intro h
      exact hm (Finset.mem_biUnion.mpr ⟨a, h, ha⟩)
    simp [supportedCoefficient, hn]
  ext i
  fin_cases i <;> simp only [localVector, Pi.zero_apply]
  · apply hz; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · apply hz; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · apply hz; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · apply hz; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · apply hz; simp only [Finset.mem_insert, Finset.mem_singleton]; omega

theorem admissible_localVector {A : Finset ℤ} {s : ℤ → ℝ}
    (hs : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01) (t m : ℤ) :
    Admissible (localVector A s t m) := by
  have h (a : ℤ) : AdmissibleValue (supportedCoefficient A s a) := by
    unfold supportedCoefficient AdmissibleValue
    split_ifs with ha
    · exact Or.inr (hs a ha)
    · exact Or.inl rfl
  intro i
  fin_cases i <;> simp only [localVector] <;> exact h _

theorem auxiliaryPsi_eq_polynomial {A : Finset ℤ} {s : ℤ → ℝ}
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a) (t : ℤ) :
    (fun x => (auxiliaryPsi (realPolynomial A s) t x : ℂ)) =
      polynomial (auxiliarySpectrum A t) (fun m => R (localVector A s t m)) := by
  apply eq_polynomial_of_fourierCoeff
  · have hr := continuous_auxiliaryR (continuous_realPolynomial A s) t
    exact Complex.continuous_ofReal.comp ((hr.add (hr.comp continuous_neg)).div_const 2)
  · intro m
    rw [paper_auxiliaryPsi_coeff hA hs]
    by_cases hm : m ∈ auxiliarySpectrum A t
    · simp [hm]
    · simp [hm, localVector_zero_off_spectrum hm, R, localReal]

end ChowlaCosine
