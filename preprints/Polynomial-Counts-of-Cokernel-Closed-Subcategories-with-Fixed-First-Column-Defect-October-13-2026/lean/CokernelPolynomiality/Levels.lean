import CokernelPolynomiality.CodeOrder
import Mathlib.Data.Nat.Find

namespace CokernelPolynomiality

 theorem strictly_increasing_unbounded (e : ℕ → ℕ) (he : StrictMono e) (n : ℕ) : n ≤ e n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hh : e n < e (n+1) := he (Nat.lt_succ_self n)
    change n+1 ≤ e (n+1)
    omega

/-- First expanded coordinate level at or above the given regular rank. -/
noncomputable def levelCeil (e : ℕ → ℕ) (he : StrictMono e) (r : ℕ) : ℕ :=
  Nat.find (show ∃ n, r ≤ e n from ⟨r,strictly_increasing_unbounded e he r⟩)

 theorem levelCeil_spec (e : ℕ → ℕ) (he : StrictMono e) (r : ℕ) :
    r ≤ e (levelCeil e he r) := by
  unfold levelCeil
  exact Nat.find_spec (show ∃ n, r ≤ e n from ⟨r, strictly_increasing_unbounded e he r⟩)

 theorem levelCeil_le_iff (e : ℕ → ℕ) (he : StrictMono e) (r k : ℕ) :
    levelCeil e he r ≤ k ↔ r ≤ e k := by
  constructor
  · intro h
    exact le_trans (levelCeil_spec e he r) (he.monotone h)
  · intro h
    exact Nat.find_min' _ h

 theorem lt_levelCeil_iff (e : ℕ → ℕ) (he : StrictMono e) (r k : ℕ) :
    k < levelCeil e he r ↔ e k < r := by
  rw [← not_le, levelCeil_le_iff, not_le]

 theorem levelCeil_monotone (e : ℕ → ℕ) (he : StrictMono e) : Monotone (levelCeil e he) := by
  intro r s hrs
  apply (levelCeil_le_iff e he r _).mpr
  exact le_trans hrs (levelCeil_spec e he s)

 theorem levelCeil_at_level (e : ℕ → ℕ) (he : StrictMono e) (k : ℕ) :
    levelCeil e he (e k) = k := by
  apply Nat.le_antisymm ((levelCeil_le_iff e he (e k) k).mpr le_rfl)
  by_contra h
  have hh := he (show levelCeil e he (e k) < k by omega)
  have hs := levelCeil_spec e he (e k)
  omega

 theorem levelCeil_positive (e : ℕ → ℕ) (he : StrictMono e) (hzero : e 0 = 0)
    (r : ℕ) (hr : 0 < r) : 0 < levelCeil e he r := by
  apply (lt_levelCeil_iff e he r 0).mpr
  simpa only [hzero] using hr

end CokernelPolynomiality
