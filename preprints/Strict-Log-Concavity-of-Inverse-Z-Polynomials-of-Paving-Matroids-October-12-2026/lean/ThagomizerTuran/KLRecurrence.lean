import ThagomizerTuran.IncidenceDefinitions
import Mathlib.Algebra.Polynomial.Reverse

namespace MatroidInverseZ

open Finset Polynomial

@[simp] theorem belowHalf_coeff (r : ℕ) (p : Polynomial ℤ) (i : ℕ) :
    (belowHalf r p).coeff i = if i < (r + 1) / 2 then p.coeff i else 0 := by
  classical
  simp [belowHalf, Polynomial.coeff_monomial]

theorem belowHalf_high_coeff (r : ℕ) (p : Polynomial ℤ) (i : ℕ) (hi : r ≤ 2 * i) :
    (belowHalf r p).coeff i = 0 := by
  rw [belowHalf_coeff, ite_eq_right]
  omega

variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

theorem kl_recurrence (rank : α → ℕ) (a b : α) :
    kl rank b a = if a = b then 1 else
      -belowHalf (rank b - rank a)
        (∑ x ∈ Ioc a b, characteristic rank a x * kl rank b x) := by
  rw [kl]
  split_ifs
  · rfl
  · congr 2
    exact Finset.sum_attach _ (fun x => characteristic rank a x * kl rank b x)

/-- The recursive construction has the required strict half-rank degree bound
on each nontrivial interval. -/
theorem kl_high_coeff (rank : α → ℕ) (a b : α) (hab : a ≠ b)
    (i : ℕ) (hi : rank b - rank a ≤ 2 * i) : (kl rank b a).coeff i = 0 := by
  rw [kl_recurrence, ite_eq_right hab, Polynomial.coeff_neg, belowHalf_high_coeff _ _ _ hi]
  simp

/-- No alternative polynomial family can satisfy a different value of the same
finite-interval recursion. This is an infrastructure uniqueness theorem only. -/
theorem kl_unique_of_recurrence (rank : α → ℕ) (p : α → α → Polynomial ℤ)
    (hp : ∀ a b, p a b = if a = b then 1 else
      -belowHalf (rank b - rank a)
        (∑ x ∈ Ioc a b, characteristic rank a x * p x b)) :
    ∀ a b, p a b = kl rank b a := by
  intro a b
  generalize hn : (Icc a b).card = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    rw [hp, kl_recurrence]
    split_ifs
    · rfl
    · congr 2
      apply Finset.sum_congr rfl
      intro x hx
      rw [ih (Icc x b).card (by
        rw [← hn]
        have h := mem_Ioc.mp hx
        exact card_lt_card (Icc_ssubset_Icc_left (h.1.le.trans h.2) h.1 le_rfl)) x b rfl]

end MatroidInverseZ

namespace MatroidInverseZ

open Finset Polynomial

/-- Low-degree extraction of the defining KL functional equation. -/
theorem eq_neg_belowHalf_of_reflect (r : ℕ) (p s : Polynomial ℤ)
    (hdeg : ∀ i, r ≤ 2 * i → p.coeff i = 0)
    (heq : Polynomial.reflect r p = p + s) : p = -belowHalf r s := by
  ext i
  rw [Polynomial.coeff_neg, belowHalf_coeff]
  by_cases hi : i < (r + 1) / 2
  · rw [ite_eq_left hi]
    have hir : i ≤ r := by omega
    have hhigh : r ≤ 2 * (r - i) := by omega
    have hc := congrArg (fun q : Polynomial ℤ => q.coeff i) heq
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le hir,
      Polynomial.coeff_add, hdeg _ hhigh] at hc
    omega
  · rw [ite_eq_right hi, neg_zero]
    exact hdeg i (by omega)

variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

@[simp] theorem characteristic_self (rank : α → ℕ) (a : α) :
    characteristic rank a a = 1 := by
  simp [characteristic]

/-- The interval construction agrees with any family satisfying the standard
KL functional equation and degree condition; no explicit coefficient formula
is used in this uniqueness comparison. -/
theorem kl_eq_of_characterization (rank : α → ℕ) (p : α → α → Polynomial ℤ)
    (hdiag : ∀ a, p a a = 1)
    (hdeg : ∀ a b, a < b → ∀ i, rank b - rank a ≤ 2 * i → (p a b).coeff i = 0)
    (hrec : ∀ a b, a ≤ b →
      Polynomial.reflect (rank b - rank a) (p a b) =
        ∑ x ∈ Icc a b, characteristic rank a x * p x b) :
    ∀ a b, a ≤ b → p a b = kl rank b a := by
  intro a b hab
  generalize hn : (Icc a b).card = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases he : a = b
    · subst b
      simp [hdiag]
    have hlt : a < b := lt_of_le_of_ne hab he
    have hlocal : p a b = -belowHalf (rank b - rank a)
        (∑ x ∈ Ioc a b, characteristic rank a x * p x b) := by
      apply eq_neg_belowHalf_of_reflect _ _ _ (hdeg a b hlt)
      have h := hrec a b hab
      rw [Icc_eq_cons_Ioc hab, sum_cons, characteristic_self, one_mul] at h
      exact h
    rw [hlocal, kl_recurrence, ite_eq_right he]
    congr 2
    apply Finset.sum_congr rfl
    intro x hx
    have hxb := mem_Ioc.mp hx
    rw [ih (Icc x b).card (by
      rw [← hn]
      exact card_lt_card (Icc_ssubset_Icc_left (hxb.1.le.trans hxb.2) hxb.1 le_rfl))
      x b hxb.2 rfl]

end MatroidInverseZ
