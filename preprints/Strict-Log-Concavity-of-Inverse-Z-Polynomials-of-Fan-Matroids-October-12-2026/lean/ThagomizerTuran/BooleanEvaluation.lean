import ThagomizerTuran.IntervalTransport
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Evaluation on genuine Boolean flat intervals. -/
namespace MatroidInverseZ
open Finset Polynomial
variable {ι : Type*} [DecidableEq ι]

/-- The binomial sum on an actual Boolean interval. -/
theorem boolean_interval_sum {R : Type*} [CommSemiring R]
    (a b : Finset ι) (hab : a ⊆ b) (u v : R) :
    (∑ x ∈ Icc a b, u ^ (x.card - a.card) * v ^ (b.card - x.card)) =
      (u + v) ^ (b.card - a.card) := by
  rw [Finset.Icc_eq_image_powerset hab, Finset.sum_image]
  · have hc := Finset.card_sdiff_of_subset hab
    rw [← hc, ← Finset.sum_pow_mul_eq_add_pow u v (b \ a)]
    apply Finset.sum_congr rfl
    intro x hx
    have hxa : Disjoint a x := by
      apply Finset.disjoint_left.mpr
      intro i hi hix
      exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hx) hix)).2 hi
    rw [Finset.card_union_of_disjoint hxa]
    congr 2 <;> omega
  · intro x hx y hy hxy
    change a ∪ x = a ∪ y at hxy
    have hx' := Finset.mem_powerset.mp hx
    have hy' := Finset.mem_powerset.mp hy
    ext i
    constructor
    · intro hi
      have hh : i ∈ a ∪ y := by
        rw [← hxy]
        exact Finset.mem_union_right a hi
      exact (Finset.mem_union.mp hh).resolve_left (Finset.mem_sdiff.mp (hx' hi)).2
    · intro hi
      have hh : i ∈ a ∪ x := by
        rw [hxy]
        exact Finset.mem_union_right a hi
      exact (Finset.mem_union.mp hh).resolve_left (Finset.mem_sdiff.mp (hy' hi)).2

/-- Actual incidence Möbius value of a Boolean interval. -/
theorem boolean_mu (a b : Finset ι) (hab : a ⊆ b) :
    IncidenceAlgebra.mu ℤ a b = (-1 : ℤ) ^ (b.card - a.card) := by
  generalize hn : (Icc a b).card = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases he : a = b
    · subst b
      simp
    have hlt : a < b := lt_of_le_of_ne hab he
    have hcard : a.card < b.card := Finset.card_lt_card hlt
    have hs := boolean_interval_sum a b hab (-1 : ℤ) 1
    simp only [one_pow, mul_one, neg_add_cancel, zero_pow (by omega : b.card - a.card ≠ 0)] at hs
    rw [Icc_eq_cons_Ico hab, sum_cons] at hs
    rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne he]
    have hh : (∑ x ∈ Ico a b, IncidenceAlgebra.mu ℤ a x) =
        ∑ x ∈ Ico a b, (-1 : ℤ) ^ (x.card - a.card) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hax := mem_Ico.mp hx
      exact ih (Icc a x).card (by
        rw [← hn]
        exact card_lt_card (Icc_ssubset_Icc_right hab le_rfl hax.2)) a x hax.1 rfl
    rw [hh]
    omega

/-- The characteristic polynomial of an actual Boolean interval. -/
theorem boolean_characteristic (a b : Finset ι) (hab : a ⊆ b) :
    characteristic Finset.card a b = (X - 1 : Polynomial ℤ) ^ (b.card - a.card) := by
  rw [characteristic]
  have hs := boolean_interval_sum a b hab (-1 : Polynomial ℤ) X
  rw [show (-1 : Polynomial ℤ) + X = X - 1 by ring] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro x hx
  rw [boolean_mu a x (mem_Icc.mp hx).1, map_pow]
  simp

/-- The constant polynomial satisfies the full KL characterization on Boolean intervals. -/
theorem boolean_kl (a b : Finset ι) (hab : a ⊆ b) :
    kl Finset.card b a = 1 := by
  symm
  apply kl_eq_of_characterization Finset.card (fun _ _ => 1)
  · intro _
    rfl
  · intro x y hxy i hi
    have hc := Finset.card_lt_card hxy
    have hi0 : i ≠ 0 := by omega
    simp [Polynomial.coeff_one, hi0]
  · intro x y hxy
    rw [Polynomial.reflect_one]
    simp only [mul_one]
    have hs := boolean_interval_sum x y hxy (X - 1 : Polynomial ℤ) 1
    simp only [one_pow, mul_one, sub_add_cancel] at hs
    rw [← hs]
    apply Finset.sum_congr rfl
    intro z hz
    exact (boolean_characteristic x z (mem_Icc.mp hz).1).symm
  · exact hab

/-- The inverse KL incidence function is the Boolean Möbius function. -/
theorem boolean_klInverse (a b : Finset ι) (hab : a ⊆ b) :
    klInverse Finset.card a b = C ((-1 : ℤ) ^ (b.card - a.card)) := by
  generalize hn : (Icc a b).card = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases he : a = b
    · subst b
      simp
    rw [klInverse_recurrence, ite_eq_right he, ← boolean_mu a b hab,
      IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne he, map_neg, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    have hax := mem_Ico.mp hx
    rw [boolean_kl x b hax.2.le, mul_one,
      ih (Icc a x).card (by
        rw [← hn]
        exact card_lt_card (Icc_ssubset_Icc_right hab le_rfl hax.2)) a x hax.1 rfl,
      boolean_mu a x hax.1]

/-- The ordinary inverse-KL polynomial of a Boolean interval equals one. -/
theorem boolean_inverseKL (a b : Finset ι) (hab : a ⊆ b) :
    inverseKL Finset.card a b = 1 := by
  rw [inverseKL, boolean_klInverse a b hab, ← map_mul, ← mul_pow]
  simp

/-- The ordinary inverse-Z polynomial on an actual Boolean lattice interval. -/
theorem boolean_inverseZ (a b : Finset ι) (hab : a ⊆ b) :
    inverseZ Finset.card a b = (1 + X : Polynomial ℤ) ^ (b.card - a.card) := by
  rw [inverseZ]
  have hs := boolean_interval_sum a b hab (1 : Polynomial ℤ) X
  simp only [one_pow, one_mul] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro x hx
  rw [boolean_inverseKL a x (mem_Icc.mp hx).1, mul_one,
    boolean_mu x b (mem_Icc.mp hx).2, ← mul_pow]
  simp
end MatroidInverseZ
