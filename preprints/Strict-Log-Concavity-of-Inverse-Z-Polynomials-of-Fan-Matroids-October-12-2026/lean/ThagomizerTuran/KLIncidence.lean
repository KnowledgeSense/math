import ThagomizerTuran.KLFunctionalEquation

/-! Incidence-algebra packaging of the verified KL function and its actual inverse. -/
namespace MatroidInverseZ
open Finset Polynomial IncidenceAlgebra
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

private theorem kl_zero_of_not_le (r : α → ℕ) (a b : α) (h : ¬a ≤ b) : kl r b a = 0 := by
  have hne : a ≠ b := by intro he; subst b; exact h le_rfl
  have he : Ioc a b = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact h ((mem_Ioc.mp hx).1.le.trans (mem_Ioc.mp hx).2)
  rw [kl_recurrence, ite_eq_right hne, he, sum_empty]
  ext i
  simp [belowHalf_coeff]

private theorem klInverse_zero_of_not_le (r : α → ℕ) (a b : α) (h : ¬a ≤ b) : klInverse r a b = 0 := by
  have hne : a ≠ b := by intro he; subst b; exact h le_rfl
  have he : Ico a b = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact h ((mem_Ico.mp hx).1.trans (mem_Ico.mp hx).2.le)
  rw [klInverse_recurrence, ite_eq_right hne, he, sum_empty, neg_zero]

noncomputable def klKernel (r : α → ℕ) : IncidenceAlgebra (Polynomial ℤ) α where
  toFun a b := kl r b a
  eq_zero_of_not_le' {_ _} h := kl_zero_of_not_le r _ _ h

noncomputable def klInverseKernel (r : α → ℕ) : IncidenceAlgebra (Polynomial ℤ) α where
  toFun a b := klInverse r a b
  eq_zero_of_not_le' {_ _} h := klInverse_zero_of_not_le r _ _ h

@[simp] theorem klKernel_apply (r : α → ℕ) (a b : α) : klKernel r a b = kl r b a := rfl
@[simp] theorem klInverseKernel_apply (r : α → ℕ) (a b : α) : klInverseKernel r a b = klInverse r a b := rfl

/-- The genuine inverse construction is a left inverse in the incidence algebra. -/
theorem klInverseKernel_mul_klKernel (r : α → ℕ) : klInverseKernel r * klKernel r = 1 := by
  apply IncidenceAlgebra.ext
  intro a b hab
  rw [mul_apply, one_apply]
  exact inverse_convolution r a b hab

/-- Unit-diagonal incidence kernels have a unique left inverse. -/
theorem incidence_leftInverse_unique {R : Type*} [CommRing R]
    (p q q' : IncidenceAlgebra R α) (hp : ∀ x, p x x = 1)
    (hq : q * p = 1) (hq' : q' * p = 1) : q = q' := by
  apply IncidenceAlgebra.ext
  intro a b hab
  generalize hn : (Icc a b).card = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    have hs : (∑ x ∈ Ico a b, q a x * p x b) = ∑ x ∈ Ico a b, q' a x * p x b := by
      apply sum_congr rfl
      intro x hx
      have hax := mem_Ico.mp hx
      rw [ih (Icc a x).card (by rw [← hn]; exact card_lt_card (Icc_ssubset_Icc_right hab le_rfl hax.2))
        a x hax.1 rfl]
    have h1 := congrArg (fun f : IncidenceAlgebra R α => f a b) hq
    have h2 := congrArg (fun f : IncidenceAlgebra R α => f a b) hq'
    rw [mul_apply, Icc_eq_cons_Ico hab, sum_cons, hp, mul_one, hs] at h1
    rw [mul_apply, Icc_eq_cons_Ico hab, sum_cons, hp, mul_one] at h2
    exact add_right_cancel (h1.trans h2.symm)

end MatroidInverseZ
