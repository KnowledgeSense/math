import OscillatoryRecurrence.EndpointHankelLeading

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

/-- Monic normalization of the original Hankel determinant polynomial. -/
def normalizedHankel (n : ℕ) : ℚ[X] :=
  polynomialHankel n * C (polynomialHankel n).leadingCoeff⁻¹

/-- Monic normalization of the divided diagonal numerator. -/
def normalizedNumerator (n : ℕ) : ℚ[X] :=
  (polynomialNumerator n).divX * C ((polynomialNumerator n).divX).leadingCoeff⁻¹

theorem normalizedHankel_monic (n : ℕ) : (normalizedHankel n).Monic :=
  monic_mul_leadingCoeff_inv (polynomialHankel_ne_zero n)

theorem normalizedHankel_natDegree (n : ℕ) :
    (normalizedHankel n).natDegree = hankelDegree n := by
  rw [normalizedHankel, mul_comm, natDegree_C_mul
    (inv_ne_zero (leadingCoeff_ne_zero.mpr (polynomialHankel_ne_zero n))),
    polynomialHankel_natDegree]

theorem normalizedHankel_identity (n : ℕ) :
    C (polynomialHankel n).leadingCoeff * normalizedHankel n = polynomialHankel n := by
  have hn := leadingCoeff_ne_zero.mpr (polynomialHankel_ne_zero n)
  simp only [normalizedHankel]
  calc
    C (polynomialHankel n).leadingCoeff *
        (polynomialHankel n * C (polynomialHankel n).leadingCoeff⁻¹) =
        polynomialHankel n * C ((polynomialHankel n).leadingCoeff *
          (polynomialHankel n).leadingCoeff⁻¹) := by rw [map_mul]; ring
    _ = polynomialHankel n := by simp [hn]

theorem hankelDegree_injective {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : hankelDegree n = hankelDegree m) : n = m := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (ne_of_lt (hankelDegree_strict hn hlt)) h
  · exact (ne_of_lt (hankelDegree_strict hm hlt)) h.symm

/-- A single indexed family containing both determinant normalizations. -/
def recurrenceFamily (j : ℕ) : ℚ[X] := by
  classical
  exact if h : ∃ n, 2 ≤ n ∧ hankelDegree n = j then
    normalizedHankel (Classical.choose h)
  else if h : ∃ n, 4 ≤ n ∧ hankelDegree n - 1 = j then
    normalizedNumerator (Classical.choose h)
  else X ^ j

theorem recurrenceFamily_hankel {n : ℕ} (hn : 2 ≤ n) :
    recurrenceFamily (hankelDegree n) = normalizedHankel n := by
  classical
  have h : ∃ m, 2 ≤ m ∧ hankelDegree m = hankelDegree n := ⟨n, hn, rfl⟩
  rw [recurrenceFamily, dite_eq_left h]
  congr 1
  exact hankelDegree_injective (by have := (Classical.choose_spec h).1; omega)
    (by omega) (Classical.choose_spec h).2

theorem recurrenceFamily_numerator {n : ℕ} (hn : 4 ≤ n) :
    recurrenceFamily (hankelDegree n - 1) = normalizedNumerator n := by
  classical
  have h : ¬ ∃ m, 2 ≤ m ∧ hankelDegree m = hankelDegree n - 1 := by
    rintro ⟨m, _, he⟩
    exact numerator_index_ne_denominator hn he.symm
  have h' : ∃ m, 4 ≤ m ∧ hankelDegree m - 1 = hankelDegree n - 1 := ⟨n, hn, rfl⟩
  rw [recurrenceFamily, dite_eq_right h, dite_eq_left h']
  congr 1
  exact numerator_index_injective (Classical.choose_spec h').1 hn
    (Classical.choose_spec h').2

theorem recurrenceFamily_zero : recurrenceFamily 0 = 1 := by
  classical
  have h : ¬ ∃ n, 2 ≤ n ∧ hankelDegree n = 0 := by
    rintro ⟨n, hn, he⟩
    have hh := hankelDegree_strict (by omega : 1 ≤ 1) (by omega : 1 < n)
    rw [he] at hh
    norm_num [hankelDegree] at hh
  have h' : ¬ ∃ n, 4 ≤ n ∧ hankelDegree n - 1 = 0 := by
    rintro ⟨n, hn, he⟩
    have hh := (numerator_index_between hn).1
    omega
  simp [recurrenceFamily, h, h']

theorem polynomialHankel_two : polynomialHankel 2 = C 8 - C 4 * X := by
  change (Matrix.of (fun a b : Fin 2 => endpointMoment (a.val+b.val))).det = _
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply]
  norm_num [endpointMoment]
  norm_num only [map_ofNat]
  ring

theorem recurrenceFamily_one : recurrenceFamily 1 = X - C 2 := by
  have hi : hankelDegree 2 = 1 := by norm_num [hankelDegree]
  rw [← hi, recurrenceFamily_hankel (by omega : 2 ≤ 2)]
  have hl : (polynomialHankel 2).leadingCoeff = -4 := by
    rw [← coeff_natDegree, polynomialHankel_natDegree, hi, polynomialHankel_two]
    norm_num
  apply mul_left_cancel₀ (show C (polynomialHankel 2).leadingCoeff ≠ (0:ℚ[X]) by rw [hl]; norm_num)
  rw [normalizedHankel_identity, hl, polynomialHankel_two]
  simp only [map_neg, C_ofNat]
  ring

theorem polynomialHankel_one : polynomialHankel 1 = C 2 := by
  change (Matrix.of (fun a b : Fin 1 => endpointMoment (a.val+b.val))).det = _
  rw [Matrix.det_unique]
  norm_num [Matrix.of_apply, endpointMoment, C_ofNat]

theorem recurrenceFamily_hankel_identity {n : ℕ} (hn : 1 ≤ n) :
    C (polynomialHankel n).leadingCoeff * recurrenceFamily (hankelDegree n) =
      polynomialHankel n := by
  by_cases hn' : 2 ≤ n
  · rw [recurrenceFamily_hankel hn', normalizedHankel_identity]
  · have he : n = 1 := by omega
    subst n
    norm_num [hankelDegree, recurrenceFamily_zero, polynomialHankel_one]

end OscillatoryRecurrence
