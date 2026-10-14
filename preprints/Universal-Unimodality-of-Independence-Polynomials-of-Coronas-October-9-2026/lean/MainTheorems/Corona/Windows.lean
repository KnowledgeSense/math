import MainTheorems.Corona.Concentration
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

namespace ResearchMain.Corona

open Classical Polynomial

theorem window_card_bound (T : Finset ℕ) {t R : ℝ} (hR : 0 ≤ R)
    (hT : ∀ k ∈ T, |(k : ℝ) - t| ≤ R) : (T.card : ℝ) ≤ 2 * R + 1 := by
  by_cases he : T = ∅
  · simp only [he, Finset.card_empty, Nat.cast_zero]
    linarith
  have hn := Finset.nonempty_iff_ne_empty.mpr he
  let lo := T.min' hn
  let hi := T.max' hn
  have hlo : lo ∈ T := Finset.min'_mem _ _
  have hhi : hi ∈ T := Finset.max'_mem _ _
  have hle : lo ≤ hi := Finset.min'_le _ _ hhi
  have hsubset : T ⊆ Finset.Icc lo hi := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hk, Finset.le_max' _ _ hk⟩
  have hc := Finset.card_le_card hsubset
  rw [Nat.card_Icc] at hc
  have hc' : (T.card : ℝ) ≤ hi + 1 - lo := by
    have hcast : (T.card : ℝ) ≤ ((hi + 1 - lo : ℕ) : ℝ) := by exact_mod_cast hc
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at hcast
    exact hcast
  have h₁ := (abs_le.mp (hT lo hlo)).1
  have h₂ := (abs_le.mp (hT hi hhi)).2
  linarith

noncomputable def meanWindow (p : ℝ[X]) (R : ℝ) : Finset ℕ :=
  p.support.filter (fun k => |(k : ℝ) - mean p| ≤ R)

theorem window_mass_bound {p : ℝ[X]} (hp : NonnegativeCoefficients p) (hm : 0 < mass p)
    {R : ℝ} (hR : 0 < R) (hv : variance p ≤ R ^ 2 / 2) :
    mass p / 2 ≤ ∑ k ∈ meanWindow p R, p.coeff k := by
  let T := p.support.filter (fun (k : ℕ) => ¬|(k : ℝ) - mean p| ≤ R)
  have hT : T ⊆ p.support := Finset.filter_subset _ _
  have hc := concentration_bound hp T hT (r := R) (t := mean p) (by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    have hdist : R < |(k : ℝ) - mean p| := lt_of_not_ge hk'
    have hs : R ^ 2 ≤ |(k : ℝ) - mean p| ^ 2 := by nlinarith only [hR, hdist, abs_nonneg ((k : ℝ) - mean p)]
    simpa only [sq_abs] using hs)
  rw [centeredSum_mean p (ne_of_gt hm)] at hc
  have hmass := mul_le_mul_of_nonneg_left hv hm.le
  have hout : ∑ k ∈ T, p.coeff k ≤ mass p / 2 := by
    have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
    nlinarith only [hc, hmass, hR2]
  have hsum : (∑ k ∈ meanWindow p R, p.coeff k) + (∑ k ∈ T, p.coeff k) = mass p := by
    rw [mass_eq_sum]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  linarith

theorem window_peak {p : ℝ[X]} (hp : NonnegativeCoefficients p) (hm : 0 < mass p)
    {R : ℝ} (hR : 0 < R) (hv : variance p ≤ R ^ 2 / 2) :
    ∃ j : ℕ, |(j : ℝ) - mean p| ≤ R ∧ mass p ≤ 2 * (2 * R + 1) * p.coeff j := by
  have hw := window_mass_bound hp hm hR hv
  have hn : (meanWindow p R).Nonempty := by
    by_contra h
    have he : meanWindow p R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty] at hw
    linarith
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (meanWindow p R) (fun k => p.coeff k) hn
  have hsum : (∑ k ∈ meanWindow p R, p.coeff k) ≤ (meanWindow p R).card * p.coeff j := by
    calc
      _ ≤ ∑ _k ∈ meanWindow p R, p.coeff j := Finset.sum_le_sum (fun k hk => hmax k hk)
      _ = _ := by simp
  have hcard := window_card_bound (meanWindow p R) hR.le (fun k hk => (Finset.mem_filter.mp hk).2)
  have hbound := mul_le_mul_of_nonneg_right hcard (hp j)
  exact ⟨j, (Finset.mem_filter.mp hj).2, by linarith⟩

end ResearchMain.Corona
