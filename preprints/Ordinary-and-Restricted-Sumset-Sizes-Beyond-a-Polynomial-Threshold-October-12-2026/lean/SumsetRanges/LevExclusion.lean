import SumsetRanges.LevNormalization

open Finset
open scoped Pointwise
namespace SumsetRanges

/-- The interval bound coming from the diameter of a normalized integer set. -/
theorem card_ordinarySums_le_diameter (B : Finset ℤ) (d h : ℕ)
    (hbound : ∀ b ∈ B, 0 ≤ b ∧ b ≤ d) :
    (ordinarySums B h).card ≤ h*d+1 := by
  have hsub : ordinarySums B h ⊆ Finset.Icc (0 : ℤ) (h*d) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := (mem_ordinarySums B h x).mp hx
    apply Finset.mem_Icc.mpr
    constructor
    · exact Finset.sum_nonneg (fun i _ => (hbound _ (hv i)).1)
    · calc
        _ ≤ ∑ _i : Fin h, (d : ℤ) := Finset.sum_le_sum (fun i _ => (hbound _ (hv i)).2)
        _ = (h : ℤ) * d := by simp
  have hc := Finset.card_le_card hsub
  have he : ((h : ℤ)*d+1) = ((h*d+1 : ℕ) : ℤ) := by simp
  simpa only [Int.card_Icc, sub_zero, he, Int.toNat_natCast] using hc

/-- Iterating a lower bound on successive growth, beginning with the one-fold sumset. -/
theorem ordinarySums_linear_growth (B : Finset ℤ) (r : ℕ)
    (hgrowth : ∀ j : ℕ, 2 ≤ j →
      (ordinarySums B (j-1)).card + r ≤ (ordinarySums B j).card)
    (h : ℕ) (hh : 1 ≤ h) :
    B.card + (h-1)*r ≤ (ordinarySums B h).card := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hh
  induction s with
  | zero => simp [ordinarySums]
  | succ s ih =>
    have hs := hgrowth (1+(s+1)) (by omega)
    have he : 1+(s+1)-1 = 1+s := by omega
    rw [he] at hs
    simpa [Nat.add_mul, Nat.add_assoc] using (Nat.add_le_add_right (ih (by omega)) r).trans hs

/-- The arithmetic step in the excluded-value theorem. -/
theorem not_mem_excludedValues_of_diameter_growth (h k d n : ℕ)
    (hk : 3 ≤ k) (hh : 3 ≤ h)
    (hupper : n ≤ h*d+1)
    (hlower : k+(h-1)*min d (2*k-3) ≤ n) :
    n ∉ excludedValues h k := by
  intro hn
  obtain ⟨l, hl, hn⟩ := Finset.mem_biUnion.mp hn
  have hlrange : l < min h k - 2 := Finset.mem_range.mp hl
  have hlh : l+3 ≤ h := by omega
  have hlk : l+3 ≤ k := by omega
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
  have hk1 : k-1+1 = k := by omega
  have hh1 : h-1+1 = h := by omega
  have hhl : h-2-l+l+2 = h := by omega
  have hM : ordinaryMinimum h k = h*(k-1)+1 := by
    simp only [ordinaryMinimum, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hM] at hnlo hnhi
  by_cases hd : d ≤ 2*k-3
  · rw [min_eq_left hd] at hlower
    have hdk : k+l ≤ d := by
      by_contra hnot
      have hbad : d+1 ≤ k+l := by omega
      have hm := Nat.mul_le_mul_left h hbad
      nlinarith
    have hm := Nat.mul_le_mul_left (h-1) hdk
    nlinarith
  · have hkd : 2*k-3 ≤ d := by omega
    rw [min_eq_right hkd] at hlower
    have hk2 : 2*k-3+3 = 2*k := by omega
    have hm := Nat.mul_le_mul_left (h-1) hlk
    nlinarith

/-- Lev's growth inequality, combined with normalization, excludes every forbidden interval. -/
theorem card_ordinarySums_not_mem_excludedValues_of_growth (A : Finset ℤ) (h : ℕ)
    (hLev : ∀ (B : Finset ℤ) (d j : ℕ),
      2 ≤ B.card → 0 ∈ B → (d : ℤ) ∈ B →
      (∀ b ∈ B, 0 ≤ b ∧ b ≤ d) → B.gcd id = 1 → 2 ≤ j →
      (ordinarySums B (j-1)).card + min d (j*(B.card-2)+1) ≤
        (ordinarySums B j).card) :
    (ordinarySums A h).card ∉ excludedValues h A.card := by
  by_cases hempty : min h A.card ≤ 2
  · have hz : min h A.card - 2 = 0 := by omega
    simp [excludedValues, hz]
  have hh : 3 ≤ h := by omega
  have hk : 3 ≤ A.card := by omega
  obtain ⟨B, d, hBc, hBs, hBzero, hBd, hBb, hBg⟩ :=
    exists_ordinary_normalization A (by omega)
  have hgrowth : ∀ j : ℕ, 2 ≤ j →
      (ordinarySums B (j-1)).card + min d (2*A.card-3) ≤
        (ordinarySums B j).card := by
    intro j hj
    have he := hLev B d j (by omega) hBzero hBd hBb hBg hj
    rw [hBc] at he
    have hk2 : A.card-2+2 = A.card := by omega
    have hmul := Nat.mul_le_mul_right (A.card-2) hj
    have hstep : 2*A.card-3 ≤ j*(A.card-2)+1 := by omega
    exact (Nat.add_le_add_left (min_le_min_left d hstep) _).trans he
  have hlo := ordinarySums_linear_growth B (min d (2*A.card-3)) hgrowth h (by omega)
  rw [hBc, hBs h] at hlo
  have hhi := card_ordinarySums_le_diameter B d h hBb
  rw [hBs h] at hhi
  exact not_mem_excludedValues_of_diameter_growth h A.card d _ hk hh hhi hlo

end SumsetRanges
