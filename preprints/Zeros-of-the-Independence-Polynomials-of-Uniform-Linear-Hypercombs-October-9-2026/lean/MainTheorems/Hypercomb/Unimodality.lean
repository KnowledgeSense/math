import MainTheorems.Hypercomb.RealSequences

namespace ResearchMain.Hypercomb

theorem PositiveLC.unimodal {f : ℤ → ℝ} {e : ℕ} (hf : PositiveLC f e) :
    ∃ m : ℕ, m ≤ e ∧ (∀ k < m, f k ≤ f (k + 1)) ∧ (∀ k ≥ m, f (k + 1) ≤ f k) := by
  have hlast : f ((e : ℤ) + 1) < f e := by
    rw [hf.zero ((e : ℤ) + 1) (by omega)]
    exact hf.positive e (by omega) le_rfl
  have hex : ∃ m : ℕ, f ((m : ℤ) + 1) < f m := ⟨e, hlast⟩
  let m := Nat.find hex
  have hdrop : f ((m : ℤ) + 1) < f m := Nat.find_spec hex
  have hme : m ≤ e := Nat.find_min' hex hlast
  have hfm : 0 < f m := hf.positive m (by omega) (by exact_mod_cast hme)
  refine ⟨m, hme, ?_, ?_⟩
  · intro k hk
    have h := Nat.find_min hex hk
    exact le_of_not_gt h
  · intro k hk
    by_cases hkm : k = m
    · subst k
      exact hdrop.le
    · have hmk : (m : ℤ) + 1 ≤ k := by omega
      have hminor := hf.ratioDecreasing k ((m : ℤ) + 1) hmk
      rw [show (m : ℤ) + 1 - 1 = m by omega] at hminor
      have hbound := mul_le_mul_of_nonneg_left hdrop.le (hf.nonnegative k)
      have hresult : f ((k : ℤ) + 1) * f m ≤ f k * f m := hminor.trans hbound
      exact le_of_mul_le_mul_right hresult hfm

end ResearchMain.Hypercomb
