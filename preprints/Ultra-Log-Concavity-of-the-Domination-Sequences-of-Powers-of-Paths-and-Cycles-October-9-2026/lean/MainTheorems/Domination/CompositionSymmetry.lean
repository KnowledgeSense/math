import MainTheorems.Domination.CompositionConvolution

namespace ResearchMain.Domination

open Classical

theorem compositionCountZ_reindex {r s : ℕ} (e : Fin r ≃ Fin s)
    (bounds : Fin s → ℕ) (N : ℤ) :
    compositionCountZ (bounds ∘ e) N = compositionCountZ bounds N := by
  unfold compositionCountZ
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
    have hsum : (∑ i : Fin s, (p ∘ e.symm) i) = ∑ i : Fin r, p i :=
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    rw [hsum]

theorem compositionCountZ_concat {r s : ℕ} (a : Fin r → ℕ) (b : Fin s → ℕ)
    (N : ℤ) :
    compositionCountZ (Fin.addCases a b) N =
      ∑ p ∈ boundedParts a, compositionCountZ b (N - (∑ i, p i : ℕ)) := by
  unfold compositionCountZ
  rw [← Finset.sum_product (boundedParts a) (boundedParts b)
    (fun p : (Fin r → ℕ) × (Fin s → ℕ) =>
      if ((∑ i, p.2 i : ℕ) : ℤ) = N - (∑ i, p.1 i : ℕ) then (1 : ℤ) else 0)]
  symm
  apply Finset.sum_bij (fun p _ => Fin.addCases p.1 p.2)
  · intro p hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    apply (mem_boundedParts _ _).mpr
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using (mem_boundedParts a p.1).mp ha j
    · simpa using (mem_boundedParts b p.2).mp hb j
  · intro p _ q _ heq
    apply Prod.ext
    · funext i
      simpa using congrFun heq (Fin.castAdd s i)
    · funext i
      simpa using congrFun heq (Fin.natAdd r i)
  · intro p hp
    have h := (mem_boundedParts _ p).mp hp
    refine ⟨(fun i => p (Fin.castAdd s i), fun i => p (Fin.natAdd r i)), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · apply (mem_boundedParts _ _).mpr
        intro i
        simpa using h (Fin.castAdd s i)
      · apply (mem_boundedParts _ _).mpr
        intro i
        simpa using h (Fin.natAdd r i)
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · intro p _
    simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Nat.cast_add, eq_sub_iff_add_eq]
    rw [add_comm]

end ResearchMain.Domination
