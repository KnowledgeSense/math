import SphericalTreeFailures.TreeGeometry

namespace SphericalTreeFailures

theorem pendantPath_even (k : ℕ) :
    flag (pendantPath (2 * k)) = false ∧ (pendantPath (2 * k)).alpha = k := by
  induction k with
  | zero => simp [pendantPath, flag, ForestExpr.alpha]
  | succ k ih =>
    have he : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    simp [he, pendantPath, flag, ForestExpr.alpha, ih.1, ih.2]

theorem sphericalTree_flag (m k : ℕ) :
    flag (sphericalTree m (2 * k + 1)) = decide (m % 2 = 1) := by
  induction m with
  | zero =>
    have he : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    simpa [sphericalTree, he] using (pendantPath_even (k + 1)).1
  | succ m ih =>
    simp only [sphericalTree, flag, ih, Bool.or_self]
    by_cases hm : m % 2 = 1
    · have hn : (m + 1) % 2 ≠ 1 := by omega
      simp [hm, hn]
    · have hn : (m + 1) % 2 = 1 := by omega
      simp [hm, hn]

theorem sphericalTree_alpha_identity (m k : ℕ) :
    3 * (sphericalTree m (2 * k + 1)).alpha +
      (if flag (sphericalTree m (2 * k + 1)) then 1 else 2) =
      (3 * k + 5) * 2 ^ m := by
  induction m with
  | zero =>
    have he : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    simp [sphericalTree, he, (pendantPath_even (k + 1)).1,
      (pendantPath_even (k + 1)).2]
    omega
  | succ m ih =>
    simp only [sphericalTree, ForestExpr.alpha, flag, Bool.or_self, pow_succ, ← Nat.mul_assoc]
    cases hf : flag (sphericalTree m (2 * k + 1)) <;> simp [hf] at ih ⊢ <;> omega

/-- Exact independence number of the actual graph, including the parity correction. -/
theorem independenceNumber_identity (m k : ℕ) :
    3 * independenceNumberOfTree m (2 * k + 1) +
      (if m % 2 = 0 then 2 else 1) = (3 * k + 5) * 2 ^ m := by
  unfold independenceNumberOfTree
  rw [ForestExpr.graph_alpha]
  have h := sphericalTree_alpha_identity m k
  rw [sphericalTree_flag] at h
  by_cases hm : m % 2 = 0
  · have hn : m % 2 ≠ 1 := by omega
    simpa [hm, hn] using h
  · have hn : m % 2 = 1 := by omega
    simpa [hm, hn] using h

end SphericalTreeFailures
