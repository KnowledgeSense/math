import MainTheorems.PureOSequences.BlockMonomials
import MainTheorems.PureOSequences.Boxes

namespace ResearchMain.PureOSequences

noncomputable def paddedTriple (k : ℕ) (m : Monomial 3) : Monomial (4 + k) :=
  blockMonomial (m 0) (m 1) (m 2) 0 (fun _ => 0)

@[simp] theorem degree_paddedTriple (k : ℕ) (m : Monomial 3) :
    totalDeg (paddedTriple k m) = totalDeg m := by
  rw [paddedTriple, degree_blockMonomial]
  simp [totalDeg_eq_sum_univ, Fin.sum_univ_three]

theorem paddedTriple_mono (k : ℕ) {m n : Monomial 3} (hmn : m ≤ n) :
    paddedTriple k m ≤ paddedTriple k n := by
  simp only [paddedTriple]
  rw [blockMonomial_le]
  simp only [blockMonomial_left, blockMonomial_right]
  norm_num
  exact ⟨hmn 0, hmn 1, hmn 2⟩

theorem paddedTriple_injective (k : ℕ) : Function.Injective (paddedTriple k) := by
  intro m n heq
  have h0 : m 0 = n 0 := by
    simpa [paddedTriple] using congrArg (fun m => m (Fin.castAdd k 0)) heq
  have h1 : m 1 = n 1 := by
    simpa [paddedTriple] using congrArg (fun m => m (Fin.castAdd k 1)) heq
  have h2 : m 2 = n 2 := by
    simpa [paddedTriple] using congrArg (fun m => m (Fin.castAdd k 2)) heq
  rw [← triple_ext m, ← triple_ext n, h0, h1, h2]

theorem boxCount_paddedTriple (k : ℕ) (g : Monomial 3) (d : ℕ) :
    boxCount (paddedTriple k g) d = boxCount g d := by
  classical
  symm
  unfold boxCount
  apply Finset.card_bij (fun m _ => paddedTriple k m)
  · intro m hm
    obtain ⟨hmem, hdeg⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr
      ⟨mem_divisorsFinset_iff.mpr (paddedTriple_mono k (mem_divisorsFinset_iff.mp hmem)),
        by simpa using hdeg⟩
  · intro m _ n _ heq
    exact paddedTriple_injective k heq
  · intro n hn
    obtain ⟨hmem, hdeg⟩ := Finset.mem_filter.mp hn
    have hng := mem_divisorsFinset_iff.mp hmem
    rw [paddedTriple, blockMonomial_le] at hng
    have hz : n (Fin.castAdd k 3) = 0 := by omega
    have ht : (fun i => n (Fin.natAdd 4 i)) = fun _ => 0 := by
      funext i
      have := hng.2.2.2.2 i
      omega
    let m := triple (n (Fin.castAdd k 0)) (n (Fin.castAdd k 1)) (n (Fin.castAdd k 2))
    have hpad : paddedTriple k m = n := by
      simpa only [paddedTriple, m, triple_zero, triple_one, triple_two, hz, ht] using
        blockMonomial_ext n
    refine ⟨m, Finset.mem_filter.mpr ⟨?_, ?_⟩, hpad⟩
    · apply mem_divisorsFinset_iff.mpr
      rw [← triple_ext g, triple_le]
      simpa only [m, triple_zero, triple_one, triple_two] using
        And.intro hng.1 (And.intro hng.2.1 hng.2.2.1)
    · rw [← degree_paddedTriple k m, hpad]
      exact hdeg

end ResearchMain.PureOSequences
