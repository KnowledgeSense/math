import MainTheorems.Tuza.IntervalBlocks

namespace ResearchMain.Tuza

theorem sum_middle (n p q : ℕ) (hpq : p ≤ q) (hqn : q ≤ n) (f : Fin n → ℕ) :
    ∑ i : Fin n with p ≤ i.val ∧ i.val < q, f i =
      ∑ i : Fin (q - p), f (middleEmbedding n p q hpq hqn i) := by
  refine Finset.sum_bij (fun i hi => (⟨i.val - p, ?_⟩ : Fin (q - p))) ?_ ?_ ?_ ?_
  · have h := (Finset.mem_filter.mp hi).2
    omega
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj hij
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    have h := congrArg Fin.val hij
    dsimp at h
    omega
  · intro j _
    refine ⟨middleEmbedding n p q hpq hqn j, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [middleEmbedding_val]
      have := j.isLt
      omega
    · apply Fin.ext
      simp
  · intro i hi
    apply congrArg f
    apply Fin.ext
    have h := (Finset.mem_filter.mp hi).2
    simp only [middleEmbedding_val]
    omega

end ResearchMain.Tuza
