import MeanMaximumForests.Recursion
import Mathlib.Tactic.Linarith

/-! Deterministic sequence lemmas for the peak argument. Graph-specific
analytic assertions are not assumed as conclusions of these lemmas. -/
namespace MeanMaximumForests

theorem ratio_interval_antitone (r : ℕ → ℝ) (n a : ℕ)
    (hstep : ∀ j : ℕ, 0 < j → n ≤ 5 * j → 25 * j ≤ 17 * a → r j < r (j - 1))
    (u v : ℕ) (huv : u ≤ v) (hlo : n ≤ 5 * (u + 1))
    (hhi : 25 * v ≤ 17 * a) : r v ≤ r u := by
  induction v, huv using Nat.le_induction with
  | base => exact le_refl _
  | succ v huv ih =>
    have hprev : 25 * v ≤ 17 * a := by omega
    have hdec : r (v + 1) < r v := by
      simpa using hstep (v + 1) (by omega) (by omega) hhi
    exact hdec.le.trans (ih hprev)

theorem peak_ratio_separation (r : ℕ → ℝ) (n a k : ℕ)
    (ha : 3 ≤ a) (hk : 1 ≤ k) (hka : k ≤ a)
    (hlower : ∀ j < a, (n : ℝ) - 3 * j ≤ (j + 1) * r j)
    (hupper : ∀ j < a, (j + 1) * r j ≤ 2 * ((a : ℝ) - j))
    (hstep : ∀ j : ℕ, 0 < j → n ≤ 5 * j → 25 * j ≤ 17 * a → r j < r (j - 1))
    (hleft : 1 ≤ r (k - 1)) (hright : r k ≤ 1) :
    (∀ m < k, 1 ≤ r m) ∧ (∀ m, k ≤ m → m < a → r m ≤ 1) := by
  have hkm : k - 1 < a := by omega
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    simp only [Nat.cast_sub hk, Nat.cast_one]
  have huc := hupper (k - 1) hkm
  rw [hkcast] at huc
  have hmul : (k : ℝ) ≤ k * r (k - 1) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hleft)]
  have hkb : (3 : ℝ) * k ≤ 2 * a + 2 := by nlinarith
  have hkbn : 3 * k ≤ 2 * a + 2 := by exact_mod_cast hkb
  have hklt : k < a := by omega
  have hlc := hlower k hklt
  have hmul' : ((k : ℝ) + 1) * r k ≤ k + 1 := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k + 1) (sub_nonneg.mpr hright)]
  have hkn : n ≤ 4 * k + 1 := by
    have h : (n : ℝ) ≤ 4 * k + 1 := by nlinarith
    exact_mod_cast h
  constructor
  · intro m hmk
    by_cases hm : n ≤ 4 * m + 1
    · have hmon := ratio_interval_antitone r n a hstep m (k - 1)
        (by omega) (by omega) (by omega)
      exact hleft.trans hmon
    · have hlm := hlower m (by omega)
      have hnm : (4 : ℝ) * m + 1 < n := by exact_mod_cast (Nat.lt_of_not_ge hm)
      have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      by_contra h
      have hrm : r m < 1 := lt_of_not_ge h
      nlinarith [mul_pos hmpos (sub_pos.mpr hrm)]
  · intro m hkm hma
    by_cases hm : 2 * a < 3 * m + 1
    · have hum := hupper m hma
      have hnm : (2 : ℝ) * a < 3 * m + 1 := by exact_mod_cast hm
      have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      by_contra h
      have hrm : 1 < r m := lt_of_not_ge h
      nlinarith [mul_pos hmpos (sub_pos.mpr hrm)]
    · exact (ratio_interval_antitone r n a hstep k m hkm
        (by omega) (by omega)).trans hright

theorem sequence_le_of_steps (s : ℕ → ℝ) (u v : ℕ) (huv : u ≤ v)
    (hstep : ∀ j, u ≤ j → j < v → s j ≤ s (j + 1)) : s u ≤ s v := by
  induction v, huv using Nat.le_induction with
  | base => exact le_refl _
  | succ v huv ih =>
    exact (ih (fun j huj hjv => hstep j huj (by omega))).trans
      (hstep v huv (by omega))

theorem sequence_ge_of_steps (s : ℕ → ℝ) (u v : ℕ) (huv : u ≤ v)
    (hstep : ∀ j, u ≤ j → j < v → s (j + 1) ≤ s j) : s v ≤ s u := by
  induction v, huv using Nat.le_induction with
  | base => exact le_refl _
  | succ v huv ih =>
    exact (hstep v huv (by omega)).trans
      (ih (fun j huj hjv => hstep j huj (by omega)))

theorem global_maximum_of_ratio_separation (s : ℕ → ℝ) (a k : ℕ)
    (hka : k ≤ a) (hpos : ∀ j ≤ a, 0 < s j)
    (hleft : ∀ j < k, 1 ≤ s (j + 1) / s j)
    (hright : ∀ j, k ≤ j → j < a → s (j + 1) / s j ≤ 1) :
    ∀ m ≤ a, s m ≤ s k := by
  intro m hma
  by_cases hmk : m ≤ k
  · apply sequence_le_of_steps s m k hmk
    intro j _ hjk
    have h := (le_div_iff₀ (hpos j (by omega))).mp (hleft j hjk)
    simpa using h
  · apply sequence_ge_of_steps s k m (by omega)
    intro j hkj hjm
    have h := (div_le_iff₀ (hpos j (by omega))).mp (hright j hkj (by omega))
    simpa using h

end MeanMaximumForests
