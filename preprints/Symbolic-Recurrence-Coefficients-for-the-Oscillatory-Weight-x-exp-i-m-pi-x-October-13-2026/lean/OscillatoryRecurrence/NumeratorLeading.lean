import OscillatoryRecurrence.BorderLeading
import OscillatoryRecurrence.NormalizedFamily

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

def numeratorLeadingFactor (n : ℕ) : ℚ :=
  (n:ℚ)*(n+1)-borderLeadingFactor n

@[simp] theorem numeratorLeadingFactor_even (k : ℕ) :
    numeratorLeadingFactor (2*k)=2*(k:ℚ)*(k+1) := by
  simp only [numeratorLeadingFactor,borderLeadingFactor_even,Nat.cast_mul,Nat.cast_ofNat]
  ring

@[simp] theorem numeratorLeadingFactor_odd (k : ℕ) :
    numeratorLeadingFactor (2*k+1)=(k:ℚ)*(k+1) := by
  simp only [numeratorLeadingFactor,borderLeadingFactor_odd,Nat.cast_add,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_one]
  ring

theorem numeratorLeadingFactor_pos {n : ℕ} (hn : 2≤n) :
    0<numeratorLeadingFactor n := by
  obtain ⟨k,rfl|rfl⟩ := Nat.even_or_odd' n
  all_goals have hk : 0<k := by omega
  · rw [numeratorLeadingFactor_even]; positivity
  · rw [numeratorLeadingFactor_odd]; positivity

theorem polynomialNumerator_top_coeff {n : ℕ} (hn : 2≤n) :
    (polynomialNumerator n).coeff (hankelDegree n)=
      numeratorLeadingFactor n*(polynomialHankel n).leadingCoeff := by
  have hH : (polynomialHankel n).coeff (hankelDegree n)=
      (polynomialHankel n).leadingCoeff := by
    rw [← polynomialHankel_natDegree,coeff_natDegree]
  have hJ : (polynomialBorder n).coeff (hankelDegree n)=
      (polynomialBorder n).leadingCoeff := by
    rw [← polynomialBorder_natDegree n (by omega),coeff_natDegree]
  rw [polynomialNumerator,coeff_sub,coeff_C_mul,hH,hJ,
    polynomialBorder_leadingCoeff n (by omega)]
  simp only [numeratorLeadingFactor]
  ring

theorem polynomialNumerator_natDegree {n : ℕ} (hn : 2≤n) :
    (polynomialNumerator n).natDegree=hankelDegree n := by
  apply le_antisymm
  · calc
      _ ≤ max (C ((n:ℚ)*(n+1))*polynomialHankel n).natDegree
        (polynomialBorder n).natDegree := natDegree_sub_le _ _
      _ ≤ hankelDegree n := max_le
        ((natDegree_C_mul_le _ _).trans (le_of_eq (polynomialHankel_natDegree n)))
        (le_of_eq (polynomialBorder_natDegree n (by omega)))
  · apply le_natDegree_of_ne_zero
    rw [polynomialNumerator_top_coeff hn]
    exact mul_ne_zero (ne_of_gt (numeratorLeadingFactor_pos hn))
      (leadingCoeff_ne_zero.mpr (polynomialHankel_ne_zero n))

theorem polynomialNumerator_leadingCoeff {n : ℕ} (hn : 2≤n) :
    (polynomialNumerator n).leadingCoeff=
      numeratorLeadingFactor n*(polynomialHankel n).leadingCoeff := by
  rw [← coeff_natDegree,polynomialNumerator_natDegree hn,polynomialNumerator_top_coeff hn]

theorem polynomialNumerator_divX_natDegree {n : ℕ} (hn : 2≤n) :
    (polynomialNumerator n).divX.natDegree=hankelDegree n-1 := by
  rw [natDegree_divX_eq_natDegree_tsub_one,polynomialNumerator_natDegree hn]

theorem polynomialNumerator_divX_leadingCoeff {n : ℕ} (hn : 2≤n) :
    (polynomialNumerator n).divX.leadingCoeff=
      numeratorLeadingFactor n*(polynomialHankel n).leadingCoeff := by
  have hd : 1≤hankelDegree n := by
    have := hankelDegree_mono hn
    norm_num [hankelDegree] at this ⊢
    exact this
  rw [← coeff_natDegree,polynomialNumerator_divX_natDegree hn,coeff_divX,
    show hankelDegree n-1+1=hankelDegree n by omega,polynomialNumerator_top_coeff hn]

theorem polynomialNumerator_divX_ne_zero {n : ℕ} (hn : 2≤n) :
    (polynomialNumerator n).divX≠0 := by
  apply leadingCoeff_ne_zero.mp
  rw [polynomialNumerator_divX_leadingCoeff hn]
  exact mul_ne_zero (ne_of_gt (numeratorLeadingFactor_pos hn))
    (leadingCoeff_ne_zero.mpr (polynomialHankel_ne_zero n))

theorem normalizedNumerator_monic {n : ℕ} (hn : 2≤n) :
    (normalizedNumerator n).Monic :=
  monic_mul_leadingCoeff_inv (polynomialNumerator_divX_ne_zero hn)

theorem normalizedNumerator_natDegree {n : ℕ} (hn : 2≤n) :
    (normalizedNumerator n).natDegree=hankelDegree n-1 := by
  rw [normalizedNumerator,mul_comm,natDegree_C_mul
    (inv_ne_zero (leadingCoeff_ne_zero.mpr (polynomialNumerator_divX_ne_zero hn))),
    polynomialNumerator_divX_natDegree hn]

theorem normalizedNumerator_identity {n : ℕ} (hn : 2≤n) :
    C (numeratorLeadingFactor n*(polynomialHankel n).leadingCoeff)*
      normalizedNumerator n=(polynomialNumerator n).divX := by
  rw [← polynomialNumerator_divX_leadingCoeff hn]
  have h := leadingCoeff_ne_zero.mpr (polynomialNumerator_divX_ne_zero hn)
  simp only [normalizedNumerator]
  calc
    _ = (polynomialNumerator n).divX*C ((polynomialNumerator n).divX.leadingCoeff*
      (polynomialNumerator n).divX.leadingCoeff⁻¹) := by rw [map_mul]; ring
    _ = _ := by simp [h]

theorem recurrenceFamily_monic (j : ℕ) : (recurrenceFamily j).Monic := by
  classical
  unfold recurrenceFamily
  split_ifs with h h'
  · exact normalizedHankel_monic _
  · exact normalizedNumerator_monic (by have := (Classical.choose_spec h').1; omega)
  · exact monic_X_pow _

theorem recurrenceFamily_natDegree (j : ℕ) : (recurrenceFamily j).natDegree=j := by
  classical
  unfold recurrenceFamily
  split_ifs with h h'
  · rw [normalizedHankel_natDegree,(Classical.choose_spec h).2]
  · rw [normalizedNumerator_natDegree (by have := (Classical.choose_spec h').1; omega),
      (Classical.choose_spec h').2]
  · exact natDegree_X_pow _

theorem recurrenceFamily_numerator_identity {n : ℕ} (hn : 4≤n) :
    C (numeratorLeadingFactor n*(polynomialHankel n).leadingCoeff)*X*
      recurrenceFamily (hankelDegree n-1)=polynomialNumerator n := by
  rw [recurrenceFamily_numerator hn]
  calc
    _ = X*(C (numeratorLeadingFactor n*(polynomialHankel n).leadingCoeff)*
      normalizedNumerator n) := by ring
    _ = _ := by rw [normalizedNumerator_identity (by omega),polynomialNumerator_divX_identity]

end OscillatoryRecurrence
