import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

namespace ResearchMain.Laminar

open Classical

noncomputable def persistence {R A : Type*} (next : R → R) (active : R → A → Prop)
    (i : R) (a : A) : ℕ∞ :=
  if h : ∃ t : ℕ, ¬active (next^[t + 1] i) a then (Nat.find h : ℕ∞) else ⊤

theorem future_absence_step {R A : Type*} (next : R → R) (active : R → A → Prop)
    (i : R) (a : A) (hnext : active (next i) a) :
    (∃ t : ℕ, ¬active (next^[t + 1] i) a) ↔
      ∃ t : ℕ, ¬active (next^[t + 1] (next i)) a := by
  constructor
  · rintro ⟨t, ht⟩
    have htpos : 1 ≤ t := by
      by_contra h
      have ht0 : t = 0 := by omega
      subst t
      exact ht (by simpa using hnext)
    refine ⟨t - 1, ?_⟩
    have heq : t + 1 = (t - 1 + 1) + 1 := by omega
    rwa [heq, Function.iterate_succ_apply] at ht
  · rintro ⟨t, ht⟩
    refine ⟨t + 1, ?_⟩
    rwa [Function.iterate_succ_apply]

theorem persistence_zero_iff {R A : Type*} (next : R → R) (active : R → A → Prop)
    (i : R) (a : A) : persistence next active i a = 0 ↔ ¬active (next i) a := by
  unfold persistence
  split_ifs with h
  · constructor
    · intro hz
      have hzNat : Nat.find h = 0 := by exact_mod_cast hz
      have hs := Nat.find_spec h
      rw [hzNat] at hs
      simpa using hs
    · intro ha
      have h0 : ¬active (next^[0 + 1] i) a := by simpa using ha
      have hzNat : Nat.find h = 0 := Nat.eq_zero_of_le_zero (Nat.find_min' h h0)
      simp only [hzNat, Nat.cast_zero]
  · constructor
    · intro hz
      have hn : (⊤ : ℕ∞) ≠ 0 := by simp
      exact (hn hz).elim
    · intro ha
      exact (h ⟨0, by simpa using ha⟩).elim

theorem persistence_step {R A : Type*} (next : R → R) (active : R → A → Prop)
    (i : R) (a : A) (hnext : active (next i) a) :
    persistence next active i a = persistence next active (next i) a + 1 := by
  by_cases h : ∃ t : ℕ, ¬active (next^[t + 1] i) a
  · have hn := (future_absence_step next active i a hnext).mp h
    have hleft : 1 ≤ Nat.find h := by
      by_contra hl
      have h0 : Nat.find h = 0 := by omega
      have hs := Nat.find_spec h
      rw [h0] at hs
      exact hs (by simpa using hnext)
    have hl : Nat.find h ≤ Nat.find hn + 1 := by
      apply Nat.find_min'
      simpa only [Function.iterate_succ_apply] using Nat.find_spec hn
    have hr : Nat.find hn ≤ Nat.find h - 1 := by
      apply Nat.find_min'
      have hs := Nat.find_spec h
      have heq : Nat.find h + 1 = (Nat.find h - 1 + 1) + 1 := by omega
      rwa [heq, Function.iterate_succ_apply] at hs
    have heq : Nat.find h = Nat.find hn + 1 := by omega
    simp only [persistence, dite_eq_left h, dite_eq_left hn, heq, Nat.cast_add, Nat.cast_one]
  · have hn : ¬∃ t : ℕ, ¬active (next^[t + 1] (next i)) a :=
      fun hn => h ((future_absence_step next active i a hnext).mpr hn)
    simp only [persistence, dite_eq_right h, dite_eq_right hn, top_add]

end ResearchMain.Laminar
