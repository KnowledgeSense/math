import MeanMaximumForests.CoefficientLower
import MeanMaximumForests.GlobalModeLocalization
import MeanMaximumForests.PeakSequence

/-! A numerical and algebraic reduction of weak-peak globality to strict central
log-concavity. The analytic central log-concavity theorem is not asserted here.
The smaller endpoint `64/95` already suffices for the release's weak peaks. -/
namespace MeanMaximumForests
open Finset

theorem narrow_ratio_interval_antitone (r : ℕ → ℝ) (n a : ℕ)
    (hstep : ∀ j : ℕ, 0 < j → n ≤ 5 * j → 95 * j ≤ 64 * a → r j < r (j - 1))
    (u v : ℕ) (huv : u ≤ v) (hlo : n ≤ 5 * (u + 1))
    (hhi : 95 * v ≤ 64 * a) : r v ≤ r u := by
  induction v, huv using Nat.le_induction with
  | base => exact le_refl _
  | succ v huv ih =>
    have hprev : 95 * v ≤ 64 * a := by omega
    have hdec : r (v + 1) < r v := by
      simpa using hstep (v + 1) (by omega) (by omega) hhi
    exact hdec.le.trans (ih hprev)

theorem narrow_peak_ratio_separation (r : ℕ → ℝ) (n a k : ℕ)
    (ha : 3 ≤ a) (hk : 1 ≤ k) (hka : k ≤ a)
    (hlower : ∀ j < a, (n : ℝ) - 3 * j ≤ (j + 1) * r j)
    (hupper : ∀ j < a, (j + 1) * r j ≤ 2 * ((a : ℝ) - j))
    (hstep : ∀ j : ℕ, 0 < j → n ≤ 5 * j → 95 * j ≤ 64 * a → r j < r (j - 1))
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
    · have hmon := narrow_ratio_interval_antitone r n a hstep m (k - 1)
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
    · exact (narrow_ratio_interval_antitone r n a hstep k m hkm
        (by omega) (by omega)).trans hright

/-- Strict log-concavity on the narrower central interval makes every weak local
peak a global coefficient maximum. This is an explicit reduction, not a claim
that the central log-concavity premise has been proved. -/
theorem weakLocalPeak_global_of_central_logConcavity {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (hn : 5 ≤ Fintype.card V)
    (hc : ∀ j : ℕ, 0 < j → Fintype.card V ≤ 5 * j → 95 * j ≤ 64 * G.indepNum →
      independentSetCoefficient G univ (j - 1) * independentSetCoefficient G univ (j + 1) <
        independentSetCoefficient G univ j ^ 2)
    (k : ℕ) (hk : WeakLocalPeak G k) : GlobalCoefficientMode G k := by
  classical
  let s : ℕ → ℝ := fun j => independentSetCoefficient G univ j
  let r : ℕ → ℝ := fun j => s (j + 1) / s j
  have hp : ∀ j ≤ G.indepNum, 0 < s j := by
    intro j hj
    apply Nat.cast_pos.mpr
    apply (coefficient_pos_iff_le G univ j).mpr
    rwa [independenceNumber_univ]
  have hlow : ∀ j < G.indepNum, (Fintype.card V : ℝ) - 3 * j ≤ (j + 1) * r j := by
    intro j hj
    dsimp [r]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (hp j hj.le)).mpr
    simpa only [card_univ] using coefficient_extension_lower G hG univ j
  have hupp : ∀ j < G.indepNum, (j + 1) * r j ≤ 2 * ((G.indepNum : ℝ) - j) := by
    intro j hj
    dsimp [r]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (hp j hj.le)).mpr
    have h := coefficient_extension_upper G hG univ j
    rw [independenceNumber_univ] at h
    have hh := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at hh
    rw [Nat.cast_sub hj.le] at hh
    exact hh
  have hstep : ∀ j : ℕ, 0 < j → Fintype.card V ≤ 5 * j →
      95 * j ≤ 64 * G.indepNum → r j < r (j - 1) := by
    intro j hj hn hjα
    have hja : j ≤ G.indepNum := by omega
    have hprev : j - 1 + 1 = j := by omega
    have hh := (Nat.cast_lt (α := ℝ)).mpr (hc j hj hn hjα)
    push_cast at hh
    dsimp [r]
    rw [hprev]
    apply (div_lt_div_iff₀ (hp j hja) (hp (j - 1) (by omega))).mpr
    dsimp [s]
    nlinarith
  have hki := weakLocalPeak_interior G hG hn hk
  have ha : 3 ≤ G.indepNum := by
    have := forest_card_le_twice_indepNum G hG
    omega
  have hleft : 1 ≤ r (k - 1) := by
    dsimp [r]
    rw [show k - 1 + 1 = k by omega]
    apply (le_div_iff₀ (hp (k - 1) (by have := hk.1; omega))).mpr
    simp only [one_mul]
    dsimp [s]
    exact_mod_cast hk.2.1.resolve_left (by omega)
  have hright : r k ≤ 1 := by
    dsimp [r]
    apply (div_le_iff₀ (hp k hk.1)).mpr
    simp only [one_mul]
    dsimp [s]
    exact_mod_cast hk.2.2
  obtain ⟨hbefore, hafter⟩ := narrow_peak_ratio_separation r (Fintype.card V) G.indepNum k
    ha hki.1 hk.1 hlow hupp hstep hleft hright
  have hg := global_maximum_of_ratio_separation s G.indepNum k hk.1 hp hbefore hafter
  intro j
  by_cases hj : j ≤ G.indepNum
  · have hh := hg j hj
    dsimp [s] at hh
    exact_mod_cast hh
  · rw [coefficient_eq_zero_of_gt G univ j (by rw [independenceNumber_univ]; omega)]
    exact Nat.zero_le _

end MeanMaximumForests
