import ThagomizerTuran.CharacteristicKernel

/-! Verification of the functional equation for the interval construction. -/
namespace MatroidInverseZ
open Finset Polynomial

/-- Anti-reciprocity uniquely completes the prescribed lower half. -/
theorem reflect_neg_belowHalf (r : ℕ) (s : Polynomial ℤ)
    (hs : reflect r s = -s) :
    reflect r (-belowHalf r s) = -belowHalf r s + s := by
  ext i
  have hc := congrArg (fun p : Polynomial ℤ => p.coeff i) hs
  simp only [coeff_reflect, coeff_neg] at hc
  simp only [coeff_reflect, coeff_neg, coeff_add, belowHalf_coeff]
  by_cases hir : i ≤ r
  · rw [revAt_le hir] at hc ⊢
    by_cases hi : i < (r + 1) / 2
    · have hj : ¬r - i < (r + 1) / 2 := by omega
      rw [ite_eq_left hi, ite_eq_right hj]
      ring
    · rw [ite_eq_right hi]
      by_cases hj : r - i < (r + 1) / 2
      · rw [ite_eq_left hj]
        omega
      · rw [ite_eq_right hj]
        have he : r - i = i := by omega
        rw [he] at hc
        omega
  · rw [revAt_eq_self_of_lt (by omega)] at hc ⊢
    have hi : ¬i < (r + 1) / 2 := by omega
    rw [ite_eq_right hi]
    omega

variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

theorem kl_natDegree_le (r : α → ℕ) (a b : α) : (kl r b a).natDegree ≤ r b - r a := by
  by_cases he : a = b
  · subst b
    simp
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    exact kl_high_coeff r a b he i (by omega)

theorem characteristic_natDegree_le (r : α → ℕ) (hr : Monotone r) (a b : α) :
    (characteristic r a b).natDegree ≤ r b - r a := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [characteristic, Polynomial.finsetSum_coeff]
  apply sum_eq_zero
  intro x hx
  have hax := hr (mem_Icc.mp hx).1
  rw [coeff_C_mul_X_pow, ite_eq_right (by omega)]

end MatroidInverseZ

namespace MatroidInverseZ
open Finset Polynomial

theorem reflect_finset_sum {ι : Type*} (r : ℕ) (s : Finset ι) (f : ι → Polynomial ℤ) :
    reflect r (∑ x ∈ s, f x) = ∑ x ∈ s, reflect r (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reflect_zero]
  | @insert x s hx ih => rw [sum_insert hx, reflect_add, ih, sum_insert hx]

variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α]

/-- The recursive construction satisfies the full standard KL functional equation
on every finite interval of a monotonically ranked poset. -/
theorem kl_functional_equation (r : α → ℕ) (hr : Monotone r) (a b : α) (hab : a ≤ b) :
    reflect (r b - r a) (kl r b a) =
      ∑ x ∈ Icc a b, characteristic r a x * kl r b x := by
  generalize hn : (Icc a b).card = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases he : a = b
    · subst b
      simp [characteristic_self, reflect_one]
    let S := ∑ x ∈ Ioc a b, characteristic r a x * kl r b x
    have href : reflect (r b - r a) S =
        ∑ x ∈ Ioc a b, reflect (r x - r a) (characteristic r a x) *
          ∑ y ∈ Icc x b, characteristic r x y * kl r b y := by
      rw [show S = ∑ x ∈ Ioc a b, characteristic r a x * kl r b x from rfl,
        reflect_finset_sum]
      apply sum_congr rfl
      intro x hx
      have hax := mem_Ioc.mp hx
      have ha := hr hax.1.le
      have hb := hr hax.2
      have heq : r b - r a = (r x - r a) + (r b - r x) := by omega
      rw [heq, reflect_mul _ _ (characteristic_natDegree_le r hr a x) (kl_natDegree_le r x b)]
      rw [ih (Icc x b).card (by
        rw [← hn]
        exact card_lt_card (Icc_ssubset_Icc_left hab hax.1 le_rfl)) x b hax.2 rfl]
    have hk := characteristic_kernel_convolve r hr (fun x y => kl r y x) a b hab
    rw [Icc_eq_cons_Ioc hab, sum_cons, characteristic_self, Nat.sub_self,
      reflect_one, pow_zero, one_mul] at hk
    rw [Icc_eq_cons_Ioc hab, sum_cons, characteristic_self, one_mul] at hk
    change kl r b a + S +
      (∑ x ∈ Ioc a b, reflect (r x - r a) (characteristic r a x) *
        ∑ y ∈ Icc x b, characteristic r x y * kl r b y) = kl r b a at hk
    rw [← href] at hk
    have hanti : reflect (r b - r a) S = -S := by
      linear_combination hk
    have hp : kl r b a = -belowHalf (r b - r a) S := by
      rw [kl_recurrence, ite_eq_right he]
    rw [Icc_eq_cons_Ioc hab, sum_cons, characteristic_self, one_mul]
    change reflect (r b - r a) (kl r b a) = kl r b a + S
    rw [hp]
    exact reflect_neg_belowHalf _ _ hanti

end MatroidInverseZ

namespace MatroidInverseZ

/-- Uniqueness and existence together identify the construction with standard KL data. -/
theorem kl_characterization {α : Type*} [PartialOrder α] [LocallyFiniteOrder α]
    [DecidableEq α] [DecidableLE α] (r : α → ℕ) (hr : Monotone r) :
    (∀ a, kl r a a = 1) ∧
    (∀ a b, a ≠ b → ∀ i, r b - r a ≤ 2 * i → (kl r b a).coeff i = 0) ∧
    (∀ a b, a ≤ b → Polynomial.reflect (r b - r a) (kl r b a) =
      ∑ x ∈ Finset.Icc a b, characteristic r a x * kl r b x) :=
  ⟨kl_self r, kl_high_coeff r, kl_functional_equation r hr⟩

end MatroidInverseZ
