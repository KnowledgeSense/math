import ArithmeticSections.SeedTail
import ArithmeticSections.CosineCertificate

namespace ArithmeticSections

theorem seedRotation_rational_bounds : (38672 : ℝ) / 100000 < seedRotation ∧
    seedRotation < 38674 / 100000 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hlow : 14142 / 10000 < Real.sqrt 2 := by nlinarith
  have hhi : Real.sqrt 2 < 14143 / 10000 := by nlinarith
  unfold seedRotation
  constructor <;> linarith

/-- The exact nearest-integer distances used in the five initial checks. -/
noncomputable def seedDistance (r : ℕ) : ℝ := Real.pi * (match r with
  | 1 => seedRotation
  | 2 => 3 * seedRotation - 1
  | 3 => 2 - 5 * seedRotation
  | 4 => 3 - 7 * seedRotation
  | 5 => 9 * seedRotation - 3
  | 6 => 11 * seedRotation - 4
  | 7 => 13 * seedRotation - 5
  | _ => 0)

theorem oddDistance_seed (r : ℕ) (hr : r ∈ Finset.Icc 1 7) :
    oddDistance seedRotation r = seedDistance r := by
  have hlo := seedRotation_rational_bounds.1
  have hhi := seedRotation_rational_bounds.2
  have hr' : 1 ≤ r ∧ r ≤ 7 := Finset.mem_Icc.mp hr
  obtain ⟨hrlo, hrhi⟩ := hr'
  interval_cases r
  · have hh : round seedRotation = 0 := round_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
    norm_num [oddDistance, seedDistance, integerDistance, hh, abs_of_pos (by linarith : 0 < seedRotation)]
  · have hh : round (3 * seedRotation) = 1 := round_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
    norm_num [oddDistance, seedDistance, integerDistance, hh, abs_of_pos (by linarith : 0 < 3 * seedRotation - 1)]
  · have hh : round (5 * seedRotation) = 2 := round_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
    norm_num [oddDistance, seedDistance, integerDistance, hh, abs_of_neg (by linarith : 5 * seedRotation - 2 < 0)]
  · have hh : round (7 * seedRotation) = 3 := round_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
    norm_num [oddDistance, seedDistance, integerDistance, hh, abs_of_neg (by linarith : 7 * seedRotation - 3 < 0)]
  · have hh : round (9 * seedRotation) = 3 := round_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
    norm_num [oddDistance, seedDistance, integerDistance, hh, abs_of_pos (by linarith : 0 < 9 * seedRotation - 3)]
  · have hh : round (11 * seedRotation) = 4 := round_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
    norm_num [oddDistance, seedDistance, integerDistance, hh, abs_of_pos (by linarith : 0 < 11 * seedRotation - 4)]
  · have hh : round (13 * seedRotation) = 5 := round_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
    norm_num [oddDistance, seedDistance, integerDistance, hh, abs_of_pos (by linarith : 0 < 13 * seedRotation - 5)]

theorem seedDistance_order : seedDistance 7 < seedDistance 3 ∧ seedDistance 3 < seedDistance 2 ∧
    seedDistance 2 < seedDistance 6 ∧ seedDistance 6 < seedDistance 4 ∧
    seedDistance 4 < seedDistance 1 ∧ seedDistance 1 < seedDistance 5 := by
  have hlo := seedRotation_rational_bounds.1
  have hhi := seedRotation_rational_bounds.2
  unfold seedDistance
  norm_num only
  repeat' constructor
  all_goals apply mul_lt_mul_of_pos_left _ Real.pi_pos
  all_goals linarith

theorem firstDistance_eq_of_bounds {γ : ℝ} {k r : ℕ}
    (hr : 1 ≤ r) (hrk : r ≤ k)
    (hb : ∀ i, 1 ≤ i → i ≤ k → oddDistance γ r ≤ oddDistance γ i) :
    firstDistance γ k = oddDistance γ r := by
  apply le_antisymm (firstDistance_le hr hrk)
  unfold firstDistance
  rw [dite_eq_left (show 0 < k by omega), Finset.le_inf'_iff]
  intro i hi
  exact hb (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)

theorem secondDistance_eq_of_bounds {γ : ℝ} {k r s : ℕ}
    (hr : 1 ≤ r) (hrk : r ≤ k) (hs : 1 ≤ s) (hsk : s ≤ k) (hrs : r ≠ s)
    (horder : oddDistance γ r ≤ oddDistance γ s)
    (hb : ∀ i, 1 ≤ i → i ≤ k → i ≠ r → oddDistance γ s ≤ oddDistance γ i) :
    secondDistance γ k = oddDistance γ s := by
  have hk : 2 ≤ k := by omega
  apply le_antisymm
  · have h := secondDistance_le_pair (γ := γ) (i := r - 1) (j := s - 1)
      (by omega : r - 1 < k) (by omega : s - 1 < k) (by omega : r - 1 ≠ s - 1)
    simpa only [Nat.sub_add_cancel hr, Nat.sub_add_cancel hs, max_eq_right horder] using h
  · unfold secondDistance
    rw [dite_eq_left hk, Finset.le_inf'_iff]
    intro p hp
    simp only [distinctPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    by_cases h : p.1 + 1 = r
    · exact (hb (p.2 + 1) (by omega) (by omega) (by omega)).trans (le_max_right _ _)
    · exact (hb (p.1 + 1) (by omega) (by omega) h).trans (le_max_left _ _)

/-- Exact order statistics for the five initial conditions. -/
theorem seed_first_second_initial (k : ℕ) (hk : k ∈ Finset.Icc 2 6) :
    firstDistance seedRotation k = (if k = 2 then seedDistance 2 else seedDistance 3) ∧
    secondDistance seedRotation k = (if k = 2 then seedDistance 1 else seedDistance 2) := by
  have ho := seedDistance_order
  have h32 := ho.2.1.le
  have h26 := ho.2.2.1.le
  have h64 := ho.2.2.2.1.le
  have h41 := ho.2.2.2.2.1.le
  have h15 := ho.2.2.2.2.2.le
  have h21 := h26.trans (h64.trans h41)
  have h31 := h32.trans h21
  have h34 := h32.trans (h26.trans h64)
  have h24 := h26.trans h64
  have h35 := h31.trans h15
  have h25 := h21.trans h15
  have h36 := h32.trans h26
  obtain ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hk
  by_cases he : k = 2
  · subst k
    simp only [ite_true]
    have h12 : ∀ i, 1 ≤ i → i ≤ 2 → oddDistance seedRotation 2 ≤ oddDistance seedRotation i := by
      intro i hi hi'
      interval_cases i
      · rw [oddDistance_seed 2 (by decide), oddDistance_seed 1 (by decide)]
        exact h21
      · exact le_rfl
    have hrest : ∀ i, 1 ≤ i → i ≤ 2 → i ≠ 2 → oddDistance seedRotation 1 ≤ oddDistance seedRotation i := by
      intro i hi hi' hn
      have he : i = 1 := by omega
      subst i
      exact le_rfl
    constructor
    · rw [firstDistance_eq_of_bounds (by omega : 1 ≤ 2) (by omega : 2 ≤ 2) h12, oddDistance_seed 2 (by decide)]
    · rw [secondDistance_eq_of_bounds (by omega : 1 ≤ 2) (by omega : 2 ≤ 2)
        (by omega : 1 ≤ 1) (by omega : 1 ≤ 2) (by omega : (2 : ℕ) ≠ 1)
        (h12 1 (by omega) (by omega)) hrest, oddDistance_seed 1 (by decide)]
  · simp only [ite_eq_right he]
    have hk3 : 3 ≤ k := by omega
    have hmin : ∀ i, 1 ≤ i → i ≤ k → oddDistance seedRotation 3 ≤ oddDistance seedRotation i := by
      intro i hi hi'
      rw [oddDistance_seed 3 (by decide), oddDistance_seed i (Finset.mem_Icc.mpr ⟨hi, by omega⟩)]
      have h6 : i ≤ 6 := by omega
      interval_cases i
      · exact h31
      · exact h32
      · exact le_rfl
      · exact h34
      · exact h35
      · exact h36
    have hrest : ∀ i, 1 ≤ i → i ≤ k → i ≠ 3 → oddDistance seedRotation 2 ≤ oddDistance seedRotation i := by
      intro i hi hi' hn
      rw [oddDistance_seed 2 (by decide), oddDistance_seed i (Finset.mem_Icc.mpr ⟨hi, by omega⟩)]
      have h6 : i ≤ 6 := by omega
      interval_cases i
      · exact h21
      · exact le_rfl
      · omega
      · exact h24
      · exact h25
      · exact h26
    constructor
    · rw [firstDistance_eq_of_bounds (by omega : 1 ≤ 3) hk3 hmin, oddDistance_seed 3 (by decide)]
    · rw [secondDistance_eq_of_bounds (by omega : 1 ≤ 3) hk3
        (by omega : 1 ≤ 2) hklo (by omega : (3 : ℕ) ≠ 2)
        (hmin 2 (by omega) hklo) hrest, oddDistance_seed 2 (by decide)]

end ArithmeticSections
