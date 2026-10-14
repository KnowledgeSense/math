import Mathlib.Tactic

namespace ResearchMain.Tuza

def residualInterval (T P : ℕ) (S : ℤ) (M : ℕ) (test : ℕ → Bool) : Bool :=
  let lo : ℤ := max 0 (2 * (P : ℤ) - T + 1)
  let hi : ℤ := min M ((T : ℤ) - 2 * S - 1)
  if hi < lo then true else
    (List.range ((hi - lo).toNat + 1)).all fun delta => test (lo.toNat + delta)

theorem residualInterval_extract (T P : ℕ) (S : ℤ) (M e : ℕ) (test : ℕ → Bool)
    (hM : e ≤ M) (hP : 2 * P < T + e) (hS : 2 * (S + e) < (T : ℤ) + e)
    (h : residualInterval T P S M test = true) : test e = true := by
  let lo : ℤ := max 0 (2 * (P : ℤ) - T + 1)
  let hi : ℤ := min M ((T : ℤ) - 2 * S - 1)
  have hl0 : 0 ≤ lo := le_max_left _ _
  have hle : lo ≤ (e : ℤ) := max_le (by omega) (by omega)
  have heu : (e : ℤ) ≤ hi := le_min (by omega) (by omega)
  change (if hi < lo then true else
    (List.range ((hi - lo).toNat + 1)).all fun delta => test (lo.toNat + delta)) = true at h
  rw [ite_eq_right (by omega)] at h
  let delta := ((e : ℤ) - lo).toNat
  have hd : delta ∈ List.range ((hi - lo).toNat + 1) := List.mem_range.mpr (by omega)
  have he : lo.toNat + delta = e := by omega
  have hm := List.all_eq_true.mp h delta hd
  rwa [he] at hm

end ResearchMain.Tuza
