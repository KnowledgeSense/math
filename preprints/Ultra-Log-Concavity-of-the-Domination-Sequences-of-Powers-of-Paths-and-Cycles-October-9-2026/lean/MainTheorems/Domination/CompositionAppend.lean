import MainTheorems.Domination.CompositionMoments

namespace ResearchMain.Domination

open Classical

theorem boundedSum_lastCases {r : ℕ} (bounds : Fin r → ℕ) (b : ℕ)
    (f : (Fin (r + 1) → ℕ) → ℤ) :
    (∑ p ∈ boundedParts (Fin.lastCases b bounds), f p) =
      ∑ j ∈ Finset.Icc 1 b, ∑ p ∈ boundedParts bounds, f (Fin.lastCases j p) := by
  rw [← Finset.sum_product (Finset.Icc 1 b) (boundedParts bounds)
    (fun p : ℕ × (Fin r → ℕ) => f (Fin.lastCases p.1 p.2))]
  symm
  apply Finset.sum_bij (fun p _ => Fin.lastCases p.1 p.2)
  · intro p hp
    obtain ⟨hj, hparts⟩ := Finset.mem_product.mp hp
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj
    have hb := (mem_boundedParts bounds p.2).mp hparts
    apply (mem_boundedParts _ _).mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using And.intro hjlo hjhi
    · simpa using hb j
  · intro p _ q _ heq
    apply Prod.ext
    · simpa using congrFun heq (Fin.last r)
    · funext i
      simpa using congrFun heq i.castSucc
  · intro p hp
    have hparts := (mem_boundedParts _ p).mp hp
    refine ⟨(p (Fin.last r), fun i : Fin r => p i.castSucc), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_Icc.mpr (by simpa using hparts (Fin.last r))
      · apply (mem_boundedParts _ _).mpr
        intro i
        simpa using hparts i.castSucc
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  · intro p _
    rfl

theorem compositionMoment_append {r : ℕ} (bounds : Fin r → ℕ) (b : ℕ) (N : ℤ) :
    compositionMoment (Fin.lastCases b bounds) N (Fin.last r) =
      ∑ j ∈ Finset.Icc 1 b, (j : ℤ) * compositionCountZ bounds (N - j) := by
  unfold compositionMoment
  rw [boundedSum_lastCases]
  unfold compositionCountZ
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last,
    Nat.cast_add, eq_sub_iff_add_eq]
  split <;> simp

theorem compositionLowerMoment_append {r : ℕ} (bounds : Fin r → ℕ) (b : ℕ) (N : ℤ) :
    compositionMoment (Fin.lastCases b bounds) N (Fin.last r) -
        compositionCountZ (Fin.lastCases b bounds) N =
      ∑ j ∈ Finset.Icc 1 b, ((j : ℤ) - 1) * compositionCountZ bounds (N - j) := by
  rw [compositionMoment_append, compositionCountZ_append, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end ResearchMain.Domination
