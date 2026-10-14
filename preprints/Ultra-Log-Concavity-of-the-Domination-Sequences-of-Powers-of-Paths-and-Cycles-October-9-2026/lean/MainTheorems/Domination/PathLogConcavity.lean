import MainTheorems.Domination.MergeComparison
import MainTheorems.Domination.BinomialNormalization

namespace ResearchMain.Domination

theorem path_normalizedCount (n r ℓ : ℕ) :
    normalizedCount (pathPower n ℓ) (r + 1) =
      (pathCompositionCount r (ℓ + 1) (2 * ℓ + 1) (n + 1) : ℚ) / Nat.choose n (r + 1) := by
  have h : (dominationCount (pathPower n ℓ) (r + 1) : ℚ) =
      (pathCompositionCount r (ℓ + 1) (2 * ℓ + 1) (n + 1) : ℚ) := by
    exact_mod_cast pathPower_count_endpoints n r ℓ
  unfold normalizedCount
  simp only [Fintype.card_fin, h]

theorem pathPower_ultraLogConcave (n ℓ : ℕ) : UltraLogConcave (pathPower n ℓ) := by
  intro k hk
  have hkn : 0 < k ∧ k < n := by simpa only [Finset.mem_Ioo, Fintype.card_fin] using hk
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  by_cases hkone : k = 1
  · have hz : normalizedCount (pathPower n ℓ) 0 = 0 := by
      simp only [normalizedCount, dominationCount_zero_of_nonempty, Nat.cast_zero, zero_div]
    rw [hkone, show 1 - 1 = 0 by omega, hz, zero_mul]
    exact sq_nonneg _
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hk2
    have hkval : k = r + 2 := by omega
    rw [hkval, show r + 2 - 1 = r + 1 by omega, show r + 2 + 1 = r + 3 by omega,
      path_normalizedCount n r ℓ]
    have hi2 : r + 1 + 1 = r + 2 := by omega
    have hi3 : r + 2 + 1 = r + 3 := by omega
    rw [← hi3, path_normalizedCount n (r + 2) ℓ, ← hi2, path_normalizedCount n (r + 1) ℓ]
    apply binomial_normalized_lc n (r + 1) (by omega)
    have h := pathCompositionCount_weighted_lc r (ℓ + 1) (2 * ℓ + 1) (by omega) (by omega) (n + 1)
    have hs1 : ((n - (r + 1) : ℕ) : ℤ) = (n + 1 : ℤ) - (r + 2 : ℕ) := by omega
    have hs2 : ((n - (r + 1) - 1 : ℕ) : ℤ) = (n + 1 : ℤ) - (r + 3 : ℕ) := by omega
    rw [← hs1, ← hs2] at h
    have hc1 : r + 1 + 1 = r + 2 := by omega
    simp only [hc1]
    exact_mod_cast h

end ResearchMain.Domination
