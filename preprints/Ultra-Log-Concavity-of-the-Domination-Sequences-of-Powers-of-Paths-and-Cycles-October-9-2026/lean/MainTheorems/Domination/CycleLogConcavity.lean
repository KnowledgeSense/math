import MainTheorems.Domination.CycleEndGaps
import MainTheorems.Domination.UniformCompositions
import MainTheorems.Domination.BinomialNormalization

namespace ResearchMain.Domination

theorem cycle_normalizedCount (n k ℓ : ℕ) (hn : 1 ≤ n) (hk : k + 1 ≤ n) :
    normalizedCount (cyclePower n ℓ) (k + 1) =
      (uniformCount (k + 1) (2 * ℓ + 1) n : ℚ) / Nat.choose (n - 1) k := by
  have hcount : ((k + 1 : ℕ) : ℚ) * dominationCount (cyclePower n ℓ) (k + 1) =
      (n : ℚ) * (uniformCount (k + 1) (2 * ℓ + 1) n : ℚ) := by
    exact_mod_cast cyclePower_count_composition n k ℓ
  have hchoose : (n : ℚ) * Nat.choose (n - 1) k =
      (Nat.choose n (k + 1) : ℚ) * (k + 1) := by
    have heq : n - 1 + 1 = n := by omega
    exact_mod_cast (heq ▸ Nat.add_one_mul_choose_eq (n - 1) k)
  have hleft : (Nat.choose n (k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hk)
  have hright : (Nat.choose (n - 1) k : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega : k ≤ n - 1))
  have hnzero : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold normalizedCount
  simp only [Fintype.card_fin]
  apply (div_eq_div_iff hleft hright).mpr
  apply mul_left_cancel₀ hnzero
  calc
    (n : ℚ) * (dominationCount (cyclePower n ℓ) (k + 1) * Nat.choose (n - 1) k) =
        (dominationCount (cyclePower n ℓ) (k + 1) : ℚ) * (n * Nat.choose (n - 1) k) := by ring
    _ = (dominationCount (cyclePower n ℓ) (k + 1) : ℚ) *
        ((Nat.choose n (k + 1) : ℚ) * (k + 1)) := by rw [hchoose]
    _ = (Nat.choose n (k + 1) : ℚ) *
        (((k + 1 : ℕ) : ℚ) * dominationCount (cyclePower n ℓ) (k + 1)) := by push_cast; ring
    _ = (Nat.choose n (k + 1) : ℚ) *
        (n * (uniformCount (k + 1) (2 * ℓ + 1) n : ℚ)) := by rw [hcount]
    _ = _ := by ring

theorem cyclePower_ultraLogConcave (n ℓ : ℕ) : UltraLogConcave (cyclePower n ℓ) := by
  intro k hk
  have hkn : 0 < k ∧ k < n := by simpa only [Finset.mem_Ioo, Fintype.card_fin] using hk
  have hn : 1 ≤ n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  by_cases hkone : k = 1
  · have hz : normalizedCount (cyclePower n ℓ) 0 = 0 := by
      simp only [normalizedCount, dominationCount_zero_of_nonempty, Nat.cast_zero, zero_div]
    rw [hkone, show 1 - 1 = 0 by omega, hz, zero_mul]
    exact sq_nonneg _
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hk2
    have hkval : k = r + 2 := by omega
    rw [hkval]
    rw [show r + 2 - 1 = r + 1 by omega, show r + 2 + 1 = r + 3 by omega,
      cycle_normalizedCount n r ℓ hn (by omega)]
    have hi2 : r + 1 + 1 = r + 2 := by omega
    have hi3 : r + 2 + 1 = r + 3 := by omega
    rw [← hi3, cycle_normalizedCount n (r + 2) ℓ hn (by omega),
      ← hi2, cycle_normalizedCount n (r + 1) ℓ hn (by omega)]
    apply binomial_normalized_lc (n - 1) r (by omega)
    have h := uniformCount_weighted_lc r (2 * ℓ + 1) (by omega) (n : ℤ)
    have hs1 : ((n - 1 - r : ℕ) : ℤ) = (n : ℤ) - (r + 1 : ℕ) := by omega
    have hs2 : ((n - 1 - r - 1 : ℕ) : ℤ) = (n : ℤ) - (r + 2 : ℕ) := by omega
    rw [← hs1, ← hs2] at h
    exact_mod_cast h

end ResearchMain.Domination
