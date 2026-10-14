import MainTheorems.Tuza.MatchingFactors

namespace ResearchMain.Tuza

theorem reflection_nat_card {q : ℕ} (hq : Odd q) (t : ZMod q) :
    Nat.card (reflectionGraph t).edgeSet = q / 2 := by
  classical
  let _ : NeZero q := ⟨hq.pos.ne'⟩
  have he := reflection_card (zmod_double_injective hq) t
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, ZMod.card] at he
  have hm := Nat.odd_iff.mp hq
  omega

theorem extended_nat_card {q : ℕ} (hq : Odd q) (t : ZMod q) :
    Nat.card (extendedReflectionGraph t).edgeSet = (q + 1) / 2 := by
  classical
  let _ : NeZero q := ⟨hq.pos.ne'⟩
  have he := extended_card (zmod_double_injective hq) t
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, ZMod.card] at he
  omega

def fanCount (c q : ℕ) : ℕ := q / 2 * min c (if Even q then q - 1 else q)

@[simp]
theorem fanCount_zero (c : ℕ) : fanCount c 0 = 0 := by simp [fanCount]

theorem fanCount_odd {q : ℕ} (hq : Odd q) (c : ℕ) :
    fanCount c q = q / 2 * min c q := by
  simp [fanCount, Nat.not_even_iff_odd.mpr hq]

theorem fanCount_even {q : ℕ} (hq : Even q) (c : ℕ) :
    fanCount c q = q / 2 * min c (q - 1) := by
  simp [fanCount, hq]

theorem fanCount_lower (c q : ℕ) : (q - 1) * min c q ≤ 2 * fanCount c q := by
  by_cases hq : Even q
  · rw [fanCount_even hq]
    have hm : q % 2 = 0 := Nat.even_iff.mp hq
    by_cases hc : c < q
    · rw [min_eq_left hc.le, min_eq_left (by omega : c ≤ q - 1)]
      nlinarith [Nat.mod_add_div q 2, Nat.sub_le q 1]
    · rw [min_eq_right (by omega : q ≤ c), min_eq_right (by omega : q - 1 ≤ c)]
      nlinarith [Nat.mod_add_div q 2]
  · rw [fanCount_odd (Nat.not_even_iff_odd.mp hq)]
    have hm : q % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hq)
    have he : q - 1 = 2 * (q / 2) := by omega
    rw [he]
    exact le_of_eq (by ring)

theorem fanCount_saturated {c q : ℕ} (hc : q ≤ c) : fanCount c q = q.choose 2 := by
  by_cases hq : Even q
  · rw [fanCount_even hq, min_eq_right (by omega : q - 1 ≤ c)]
    have hm : q % 2 = 0 := Nat.even_iff.mp hq
    have he : q = 2 * (q / 2) := by omega
    rw [Nat.choose_two_right,
      show q * (q - 1) = 2 * ((q / 2) * (q - 1)) by nlinarith [he]]
    simp
  · rw [fanCount_odd (Nat.not_even_iff_odd.mp hq), min_eq_right hc]
    have hm : q % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hq)
    have he : q - 1 = 2 * (q / 2) := by omega
    rw [Nat.choose_two_right,
      show q * (q - 1) = 2 * ((q / 2) * q) by nlinarith [he]]
    simp

end ResearchMain.Tuza
