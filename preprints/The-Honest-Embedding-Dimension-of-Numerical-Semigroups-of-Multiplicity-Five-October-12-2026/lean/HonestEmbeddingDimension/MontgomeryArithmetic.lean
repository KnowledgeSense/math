import HonestEmbeddingDimension.RemainingConstructionArithmetic

namespace HonestEmbeddingDimension

/-- The generator congruent to `2a` lies among `b,c` whenever the last generator exceeds `2a`. -/
theorem montgomery_exceptional_generator {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) (hdgt : 2 * a < d) :
    ∃ s : Fin 3, s ≠ 0 ∧ (![a, b, c] s) % 5 = (2 * a) % 5 ∧ ![a, b, c] s < 2 * a := by
  obtain ⟨_, ha, hb, hc, _⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have ha0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 ha (by omega)
  have hmem := S.aperyMin_mem_apery 5 hm.1 (2 * a)
  rw [five_generator_apery_set hm h] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hmod := S.aperyMin_mod 5 hm.1 (2 * a)
  have hle : S.aperyMin 5 hm.1 (2 * a) ≤ 2 * a := by
    apply NumericalSemigroup.aperyMin_le _ rfl
    simpa [Nat.mul_comm] using NumericalSemigroup.mul_mem ha.2.1 2
  rcases hmem with heq | heq | heq | heq | heq
  · rw [heq] at hmod
    omega
  · rw [heq] at hmod
    omega
  · rw [heq] at hmod
    have hlt : b < 2 * a := NumericalSemigroup.minimalGenerator_lt_multiple_of_same_residue
      hm.1 hm.2.1 hb (by omega) ha.2.1 ha.1 (by omega) hmod
    exact ⟨1, by decide, hmod, hlt⟩
  · rw [heq] at hmod
    have hlt : c < 2 * a := NumericalSemigroup.minimalGenerator_lt_multiple_of_same_residue
      hm.1 hm.2.1 hc (by omega) ha.2.1 ha.1 (by omega) hmod
    exact ⟨2, by decide, hmod, hlt⟩
  · omega

/-- Every semigroup value below `d` is a parameter multiple of `0,a,b,c`. -/
theorem five_generator_reduction_below_last {S : NumericalSemigroup} {a b c d n : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d)
    (hn : n ∈ S.monoid) (hnd : n < d) :
    ∃ j : Fin 4, ∃ q : ℕ, n = 5 * q + ![0, a, b, c] j := by
  have hle : S.aperyMin 5 hm.1 n ≤ n := NumericalSemigroup.aperyMin_le hn rfl
  have hmod := S.aperyMin_mod 5 hm.1 n
  obtain ⟨q, hq⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod
  have hmem := S.aperyMin_mem_apery 5 hm.1 n
  rw [five_generator_apery_set hm h] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with heq | heq | heq | heq | heq
  · exact ⟨0, q, by dsimp; omega⟩
  · exact ⟨1, q, by dsimp; omega⟩
  · exact ⟨2, q, by dsimp; omega⟩
  · exact ⟨3, q, by dsimp; omega⟩
  · omega

end HonestEmbeddingDimension
