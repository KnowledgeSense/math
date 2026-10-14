import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-! Ordinary inverse-Z infrastructure on actual finite ranked flat intervals.
The full Kazhdan–Lusztig functional equation is proved in
`KLFunctionalEquation`; no family log-concavity theorem is asserted here. -/
namespace MatroidInverseZ

open Finset Polynomial

variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

/-- Characteristic polynomial of a ranked interval, using its actual Möbius function. -/
noncomputable def characteristic (rank : α → ℕ) (a b : α) : Polynomial ℤ :=
  ∑ x ∈ Icc a b, Polynomial.C (IncidenceAlgebra.mu ℤ a x) *
    Polynomial.X ^ (rank b - rank x)

/-- The part strictly below half of the indicated interval rank. -/
noncomputable def belowHalf (r : ℕ) (p : Polynomial ℤ) : Polynomial ℤ :=
  ∑ i ∈ range ((r + 1) / 2), Polynomial.monomial i (p.coeff i)

/-- Recursive low-degree Kazhdan–Lusztig construction on finite ranked intervals. -/
noncomputable def kl (rank : α → ℕ) (b : α) : α → Polynomial ℤ
  | a => if a = b then 1 else
    -belowHalf (rank b - rank a)
      (∑ x ∈ (Ioc a b).attach,
        have : (Icc (x : α) b).card < (Icc a b).card := by
          have h := mem_Ioc.mp x.property
          exact card_lt_card (Icc_ssubset_Icc_left (h.1.le.trans h.2) h.1 le_rfl)
        characteristic rank a x * kl rank b x)
termination_by a => (Icc a b).card

/-- Convolution inverse of the recursively constructed KL interval function. -/
noncomputable def klInverse (rank : α → ℕ) (a : α) : α → Polynomial ℤ
  | b => if a = b then 1 else
    -(∑ x ∈ (Ico a b).attach,
      have : (Icc a (x : α)).card < (Icc a b).card := by
        have h := mem_Ico.mp x.property
        exact card_lt_card (Icc_ssubset_Icc_right (h.1.trans h.2.le) le_rfl h.2)
      klInverse rank a x * kl rank b x)
termination_by b => (Icc a b).card

/-- Ordinary inverse-KL sign convention. -/
noncomputable def inverseKL (rank : α → ℕ) (a b : α) : Polynomial ℤ :=
  Polynomial.C ((-1 : ℤ) ^ (rank b - rank a)) * klInverse rank a b

/-- Ordinary inverse-Z convention, assembled from actual interval data. -/
noncomputable def inverseZ (rank : α → ℕ) (a b : α) : Polynomial ℤ :=
  ∑ x ∈ Icc a b,
    Polynomial.C (((-1 : ℤ) ^ (rank b - rank x)) * IncidenceAlgebra.mu ℤ x b) *
      Polynomial.X ^ (rank b - rank x) * inverseKL rank a x

@[simp] theorem kl_self (rank : α → ℕ) (a : α) : kl rank a a = 1 := by
  rw [kl]
  simp

@[simp] theorem klInverse_self (rank : α → ℕ) (a : α) : klInverse rank a a = 1 := by
  rw [klInverse]
  simp

@[simp] theorem inverseKL_self (rank : α → ℕ) (a : α) : inverseKL rank a a = 1 := by
  simp [inverseKL]

@[simp] theorem inverseZ_self (rank : α → ℕ) (a : α) : inverseZ rank a a = 1 := by
  simp [inverseZ]

end MatroidInverseZ

namespace MatroidInverseZ

open Finset Polynomial

variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

theorem klInverse_recurrence (rank : α → ℕ) (a b : α) :
    klInverse rank a b = if a = b then 1 else
      -∑ x ∈ Ico a b, klInverse rank a x * kl rank b x := by
  rw [klInverse]
  split_ifs
  · rfl
  · congr 1
    exact Finset.sum_attach _ (fun x => klInverse rank a x * kl rank b x)

/-- The inverse construction genuinely inverts the KL interval function on every interval. -/
theorem inverse_convolution (rank : α → ℕ) (a b : α) (hab : a ≤ b) :
    ∑ x ∈ Icc a b, klInverse rank a x * kl rank b x = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst b
    simp
  · rw [ite_eq_right h, Icc_eq_cons_Ico hab, sum_cons]
    rw [kl_self, mul_one, klInverse_recurrence, ite_eq_right h]
    exact neg_add_cancel _

end MatroidInverseZ
