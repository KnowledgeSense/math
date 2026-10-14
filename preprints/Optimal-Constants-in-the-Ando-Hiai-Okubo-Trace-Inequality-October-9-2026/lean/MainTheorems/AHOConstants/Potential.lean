import MainTheorems.AHOConstants.Circulation
import Mathlib.Order.Interval.Finset.Fin

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {m : ℕ}

noncomputable def cyclicPotential (p q : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => j.val < i.val),
    (p (finRotate (m + 1) j) - q j)

theorem cyclicPotential_zero (p q : Fin (m + 1) → ℝ) :
    cyclicPotential p q 0 = 0 := by
  simp [cyclicPotential]

theorem cyclicPotential_step (p q : Fin (m + 1) → ℝ)
    (ht : (∑ i, p i) = ∑ i, q i) (i : Fin (m + 1)) :
    cyclicPotential p q (finRotate (m + 1) i) - cyclicPotential p q i =
      p (finRotate (m + 1) i) - q i := by
  classical
  by_cases hi : i = Fin.last m
  · subst i
    rw [finRotate_last, cyclicPotential_zero]
    have hs :
        (∑ j : Fin (m + 1), (p (finRotate (m + 1) j) - q j)) = 0 := by
      rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate (m + 1)) p, ht]
      ring
    have hu :
        insert (Fin.last m)
          (Finset.univ.filter (fun j : Fin (m + 1) => j.val < (Fin.last m).val)) =
          Finset.univ := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.val_last, iff_true]
      by_cases hj : j = Fin.last m
      · exact Or.inl hj
      · right
        have hjval : j.val ≠ m := by
          intro h
          apply hj
          apply Fin.ext
          exact h
        omega
    have hn : Fin.last m ∉
        Finset.univ.filter (fun j : Fin (m + 1) => j.val < (Fin.last m).val) := by
      simp
    rw [← hu, Finset.sum_insert hn] at hs
    dsimp [cyclicPotential]
    rw [finRotate_last] at hs
    simp only [Fin.val_last] at hs
    linarith
  · have hv := coe_finRotate_of_ne_last hi
    have hu :
        Finset.univ.filter (fun j : Fin (m + 1) => j.val <
          (finRotate (m + 1) i).val) =
        insert i (Finset.univ.filter (fun j : Fin (m + 1) => j.val < i.val)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      rw [hv]
      constructor
      · intro h
        by_cases hj : j.val = i.val
        · exact Or.inl (Fin.ext hj)
        · exact Or.inr (by omega)
      · rintro (rfl | h) <;> omega
    have hn : i ∉ Finset.univ.filter (fun j : Fin (m + 1) => j.val < i.val) := by
      simp
    simp only [cyclicPotential, hu, Finset.sum_insert hn]
    ring

theorem rotation_invariant_constant (f : Fin (m + 1) → ℝ)
    (h : ∀ i, f (finRotate (m + 1) i) = f i) (i : Fin (m + 1)) : f i = f 0 := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi' : i < m := by omega
    have hr := h ⟨i, by omega⟩
    rw [finRotate_of_lt hi'] at hr
    exact hr.trans (ih (by omega))

theorem Circulation.affine {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) (i : Fin (m + 1)) :
    a i = a 0 + cyclicPotential p q i := by
  have hc := rotation_invariant_constant
    (fun j => a j - cyclicPotential p q j) (fun j => by
      have h₁ := h.step j
      have h₂ := cyclicPotential_step p q h.total j
      linarith) i
  rw [cyclicPotential_zero] at hc
  linarith

end ResearchMain.AHOConstants
