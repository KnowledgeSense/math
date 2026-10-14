import OscillatoryRecurrence.ConstantBorder

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

/-- The polynomial numerator of the diagonal recurrence correction. -/
def polynomialNumerator (n : ℕ) : ℚ[X] :=
  C ((n:ℚ)*(n+1))*polynomialHankel n-polynomialBorder n

theorem polynomialNumerator_eval_zero (n : ℕ) :
    (polynomialNumerator n).eval 0=0 := by
  simp [polynomialNumerator,polynomialBorder_eval_zero]

theorem polynomialNumerator_coeff_zero (n : ℕ) :
    (polynomialNumerator n).coeff 0=0 := by
  rw [coeff_zero_eq_eval_zero,polynomialNumerator_eval_zero]

theorem polynomialNumerator_X_dvd (n : ℕ) : X ∣ polynomialNumerator n :=
  X_dvd_iff.mpr (polynomialNumerator_coeff_zero n)

theorem polynomialNumerator_divX_identity (n : ℕ) :
    X*(polynomialNumerator n).divX=polynomialNumerator n := by
  simpa [polynomialNumerator_coeff_zero] using X_mul_divX_add (polynomialNumerator n)

/-- The index of the full determinant in the common monic family. -/
def hankelDegree (n : ℕ) : ℕ := (n/2)*((n+1)/2)

@[simp] theorem hankelDegree_even (k : ℕ) : hankelDegree (2*k)=k^2 := by
  simp [hankelDegree,Nat.add_div,pow_two]

@[simp] theorem hankelDegree_odd (k : ℕ) : hankelDegree (2*k+1)=k*(k+1) := by
  simp [hankelDegree,Nat.add_div]

 theorem hankelDegree_eq (n : ℕ) : hankelDegree n=n^2/4 := by
  obtain ⟨k,rfl|rfl⟩ := Nat.even_or_odd' n
  · rw [hankelDegree_even]
    have he : (2*k)^2=k^2*4 := by ring
    rw [he,Nat.mul_div_left _ (by norm_num)]
  · rw [hankelDegree_odd]
    have he : (2*k+1)^2=k*(k+1)*4+1 := by ring
    rw [he,Nat.add_div]
    all_goals norm_num

 theorem hankelDegree_succ (n : ℕ) :
    hankelDegree (n+1)=hankelDegree n+(n+1)/2 := by
  obtain ⟨k,rfl|rfl⟩ := Nat.even_or_odd' n
  · rw [hankelDegree_odd,hankelDegree_even]
    simp [Nat.add_div]
    ring
  · rw [show 2*k+1+1=2*(k+1) by omega,hankelDegree_even,hankelDegree_odd]
    simp
    ring

 theorem hankelDegree_mono : Monotone hankelDegree := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hankelDegree_succ]
  omega

 theorem hankelDegree_strict {a b : ℕ} (ha : 1≤a) (hab : a<b) :
    hankelDegree a<hankelDegree b := by
  have h := hankelDegree_mono (show a+1≤b by omega)
  rw [hankelDegree_succ] at h
  have : 1≤(a+1)/2 := by omega
  omega

 theorem hankelDegree_gap {n : ℕ} (hn : 4≤n) :
    hankelDegree (n-1)+2≤hankelDegree n := by
  have h := hankelDegree_succ (n-1)
  rw [show n-1+1=n by omega] at h
  have : 2≤n/2 := by omega
  omega

 theorem numerator_index_between {n : ℕ} (hn : 4≤n) :
    hankelDegree (n-1)<hankelDegree n-1 ∧ hankelDegree n-1<hankelDegree n := by
  have := hankelDegree_gap hn
  omega

 theorem numerator_index_ne_denominator {n m : ℕ} (hn : 4≤n) :
    hankelDegree n-1≠hankelDegree m := by
  obtain ⟨hleft,hright⟩ := numerator_index_between hn
  by_cases hm : m<n
  · have := hankelDegree_mono (show m≤n-1 by omega)
    omega
  · have := hankelDegree_mono (show n≤m by omega)
    omega

 theorem numerator_index_injective {n m : ℕ} (hn : 4≤n) (hm : 4≤m)
    (h : hankelDegree n-1=hankelDegree m-1) : n=m := by
  have hp := (numerator_index_between hn).2
  have hq := (numerator_index_between hm).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hlt
  · have := hankelDegree_strict (by omega : 1≤n) hlt
    omega
  · have := hankelDegree_strict (by omega : 1≤m) hlt
    omega

end OscillatoryRecurrence
