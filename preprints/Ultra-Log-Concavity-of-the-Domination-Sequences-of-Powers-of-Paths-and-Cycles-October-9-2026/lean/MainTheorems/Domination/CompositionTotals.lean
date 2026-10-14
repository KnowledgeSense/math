import MainTheorems.Domination.CompositionSymmetry

namespace ResearchMain.Domination

open Classical

theorem parts_sum_le {r : ℕ} (bounds : Fin r → ℕ) (p : Fin r → ℕ)
    (hp : p ∈ boundedParts bounds) : (∑ i, p i) ≤ ∑ i, bounds i := by
  apply Finset.sum_le_sum
  intro i _
  exact ((mem_boundedParts _ _).mp hp i).2

theorem composition_sum_by_total {r : ℕ} (bounds : Fin r → ℕ) (f : ℤ → ℤ) :
    (∑ p ∈ boundedParts bounds, f (∑ i, p i : ℕ)) =
      ∑ t ∈ Finset.Icc 0 (∑ i, bounds i), compositionCountZ bounds t * f t := by
  unfold compositionCountZ
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  symm
  rw [Finset.sum_eq_single (∑ i, p i)]
  · simp only [ite_true, one_mul]
  · intro t _ ht
    have hne : ((∑ i, p i : ℕ) : ℤ) ≠ t := by exact_mod_cast Ne.symm ht
    simp only [hne, ite_false, zero_mul]
  · intro ht
    exact False.elim (ht (Finset.mem_Icc.mpr ⟨Nat.zero_le _, parts_sum_le bounds p hp⟩))

theorem compositionCountZ_convolution {r s : ℕ} (a : Fin r → ℕ) (b : Fin s → ℕ)
    (N : ℤ) :
    compositionCountZ (Fin.addCases a b) N =
      ∑ t ∈ Finset.Icc 0 (∑ i, a i),
        compositionCountZ a t * compositionCountZ b (N - t) := by
  rw [compositionCountZ_concat]
  exact composition_sum_by_total a (fun t => compositionCountZ b (N - t))

end ResearchMain.Domination
