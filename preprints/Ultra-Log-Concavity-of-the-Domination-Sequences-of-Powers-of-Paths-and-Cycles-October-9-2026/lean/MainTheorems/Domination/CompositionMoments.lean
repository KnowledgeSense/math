import MainTheorems.Domination.CompositionTotals

namespace ResearchMain.Domination

open Classical

theorem boundedSum_reindex {r s : ℕ} (e : Fin r ≃ Fin s) (bounds : Fin s → ℕ)
    (f : (Fin s → ℕ) → ℤ) :
    (∑ p ∈ boundedParts (bounds ∘ e), f (p ∘ e.symm)) =
      ∑ p ∈ boundedParts bounds, f p := by
  apply Finset.sum_bij (fun p _ => p ∘ e.symm)
  · intro p hp
    have h := (mem_boundedParts _ p).mp hp
    apply (mem_boundedParts _ _).mpr
    intro i
    simpa only [Function.comp_apply, e.apply_symm_apply] using h (e.symm i)
  · intro p _ q _ heq
    funext i
    have h := congrFun heq (e i)
    simpa only [Function.comp_apply, e.symm_apply_apply] using h
  · intro p hp
    refine ⟨p ∘ e, ?_, ?_⟩
    · apply (mem_boundedParts _ _).mpr
      intro i
      exact (mem_boundedParts _ p).mp hp (e i)
    · funext i
      simp only [Function.comp_apply, e.apply_symm_apply]
  · intro p _
    rfl

noncomputable def compositionMoment {r : ℕ} (bounds : Fin r → ℕ) (N : ℤ)
    (i : Fin r) : ℤ :=
  ∑ p ∈ boundedParts bounds, if ((∑ j, p j : ℕ) : ℤ) = N then (p i : ℤ) else 0

theorem compositionMoment_reindex {r s : ℕ} (e : Fin r ≃ Fin s)
    (bounds : Fin s → ℕ) (N : ℤ) (i : Fin r) :
    compositionMoment (bounds ∘ e) N i = compositionMoment bounds N (e i) := by
  unfold compositionMoment
  have h := boundedSum_reindex e bounds
    (fun p => if ((∑ j, p j : ℕ) : ℤ) = N then (p (e i) : ℤ) else 0)
  rw [← h]
  apply Finset.sum_congr rfl
  intro p _
  have hsum : (∑ j : Fin s, p (e.symm j)) = ∑ j : Fin r, p j :=
    Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  simp only [Function.comp_apply, e.symm_apply_apply]
  rw [hsum]

theorem uniform_compositionMoment_eq {r : ℕ} (m : ℕ) (N : ℤ) (i j : Fin r) :
    compositionMoment (fun _ : Fin r => m) N i =
      compositionMoment (fun _ : Fin r => m) N j := by
  have h := compositionMoment_reindex (Equiv.swap i j) (fun _ : Fin r => m) N i
  simpa only [Function.comp_def, Equiv.swap_apply_left] using h

theorem sum_compositionMoment {r : ℕ} (bounds : Fin r → ℕ) (N : ℤ) :
    (∑ i, compositionMoment bounds N i) = N * compositionCountZ bounds N := by
  unfold compositionMoment compositionCountZ
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : ((∑ i, p i : ℕ) : ℤ) = N
  · simp only [h, ite_true, mul_one]
    exact_mod_cast h
  · simp only [h, ite_false, Finset.sum_const_zero, mul_zero]

theorem uniform_compositionMoment {r : ℕ} (m : ℕ) (N : ℤ) (i : Fin r) :
    (r : ℤ) * compositionMoment (fun _ : Fin r => m) N i =
      N * compositionCountZ (fun _ : Fin r => m) N := by
  rw [← sum_compositionMoment]
  calc
    (r : ℤ) * compositionMoment (fun _ : Fin r => m) N i =
        ∑ _j : Fin r, compositionMoment (fun _ : Fin r => m) N i := by simp
    _ = ∑ j : Fin r, compositionMoment (fun _ : Fin r => m) N j := by
      apply Finset.sum_congr rfl
      intro j _
      exact uniform_compositionMoment_eq m N i j

end ResearchMain.Domination
