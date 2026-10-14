import MainTheorems.Domination.Compositions
import MainTheorems.LogConcavity

namespace ResearchMain.Domination

open Classical ResearchMain.PureOSequences ResearchMain.LogConcavity

theorem compositionCountZ_append {r : ℕ} (bounds : Fin r → ℕ) (b : ℕ) (N : ℤ) :
    compositionCountZ (Fin.lastCases b bounds) N =
      ∑ j ∈ Finset.Icc 1 b, compositionCountZ bounds (N - j) := by
  unfold compositionCountZ
  rw [← Finset.sum_product (Finset.Icc 1 b) (boundedParts bounds)
    (fun p : ℕ × (Fin r → ℕ) =>
      if ((∑ i, p.2 i : ℕ) : ℤ) = N - p.1 then (1 : ℤ) else 0)]
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
      · apply (mem_boundedParts bounds _).mpr
        intro i
        simpa using hparts i.castSucc
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  · intro p _
    simp only [Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last,
      Nat.cast_add, eq_sub_iff_add_eq]

theorem composition_append_minor {r : ℕ} (bounds : Fin r → ℕ)
    (hpos : ∀ i, 1 ≤ bounds i) (b : ℕ) (u v : ℤ) (huv : u ≤ v) :
    compositionCountZ (Fin.lastCases b bounds) u * compositionCountZ bounds v ≤
      compositionCountZ bounds u * compositionCountZ (Fin.lastCases b bounds) v := by
  rw [compositionCountZ_append, compositionCountZ_append]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact shifted_minor (compositionCountZ_ratioDecreasing bounds hpos) u v j huv (by omega)

theorem composition_conditioning_cumulative {r : ℕ} (bounds : Fin r → ℕ)
    (hpos : ∀ i, 1 ≤ bounds i) (b : ℕ) (c : ℤ → ℤ) (S : Finset ℤ)
    (hc : ∀ s ∈ S, 0 ≤ c s) (N a : ℤ) :
    (∑ s ∈ S.filter (· ≤ a), c s * compositionCountZ bounds (N - s)) *
      (∑ s ∈ S, c s * compositionCountZ (Fin.lastCases b bounds) (N - s)) ≤
    (∑ s ∈ S.filter (· ≤ a), c s * compositionCountZ (Fin.lastCases b bounds) (N - s)) *
      (∑ s ∈ S, c s * compositionCountZ bounds (N - s)) := by
  exact conditioning_cumulative S hc (composition_append_minor bounds hpos b) N a

end ResearchMain.Domination
