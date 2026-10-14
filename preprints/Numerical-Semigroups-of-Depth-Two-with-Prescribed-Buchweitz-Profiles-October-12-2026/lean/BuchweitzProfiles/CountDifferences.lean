import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace BuchweitzProfiles

/-- The square contribution of the small-generator rows. -/
def smallRowCount (K n : Nat) : Int := ((min n K + 1 : Nat) : Int)^2

/-- The exact contribution of a large generator, as in Proposition 4.3. -/
def largeRowCount (d t n : Nat) : Int :=
  ((min (n - 1) (d - 2) + 1 : Nat) : Int)^2 + if d ≤ n then (t : Int) else 0

lemma smallRowCount_difference (K n : Nat) (hn : 1 ≤ n) :
    smallRowCount K n - smallRowCount K (n - 1) =
      if n ≤ K then 2 * (n : Int) + 1 else 0 := by
  unfold smallRowCount
  by_cases h : n ≤ K
  · have h1 : min n K + 1 = n + 1 := by omega
    have h2 : min (n - 1) K + 1 = n := by omega
    rw [h1, h2, ite_eq_left h]
    push_cast
    ring
  · have h1 : min n K + 1 = K + 1 := by omega
    have h2 : min (n - 1) K + 1 = K + 1 := by omega
    rw [h1, h2, ite_eq_right h]
    ring

lemma largeRowCount_difference (d t n : Nat) (hd : 2 ≤ d) (hn : 2 ≤ n) :
    largeRowCount d t n - largeRowCount d t (n - 1) =
      (if n + 1 ≤ d then 2 * (n : Int) - 1 else 0) +
      (if n = d then (t : Int) else 0) := by
  unfold largeRowCount
  by_cases hlow : n < d
  · have h1 : min (n - 1) (d - 2) + 1 = n := by omega
    have h2 : min (n - 1 - 1) (d - 2) + 1 = n - 1 := by omega
    rw [h1, h2, ite_eq_right (by omega : ¬ d ≤ n), ite_eq_right (by omega : ¬ d ≤ n - 1),
      ite_eq_left (by omega : n + 1 ≤ d), ite_eq_right (by omega : n ≠ d)]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  by_cases heq : n = d
  · subst n
    have h1 : min (d - 1) (d - 2) + 1 = d - 1 := by omega
    have h2 : min (d - 1 - 1) (d - 2) + 1 = d - 1 := by omega
    rw [h1, h2, ite_eq_left (by omega : d ≤ d), ite_eq_right (by omega : ¬ d ≤ d - 1),
      ite_eq_right (by omega : ¬ d + 1 ≤ d), ite_eq_left rfl]
    ring
  · have h1 : min (n - 1) (d - 2) + 1 = d - 1 := by omega
    have h2 : min (n - 1 - 1) (d - 2) + 1 = d - 1 := by omega
    rw [h1, h2, ite_eq_left (by omega : d ≤ n), ite_eq_left (by omega : d ≤ n - 1),
      ite_eq_right (by omega : ¬ n + 1 ≤ d), ite_eq_right heq]
    ring

/-- The right side of the count formula, separated from the sumset theorem. -/
def rowCount {ι : Type*} (J : Finset ι) (K : Nat) (d t : ι → Nat) (n : Nat) : Int :=
  smallRowCount K n + ∑ j ∈ J, largeRowCount (d j) (t j) n

theorem rowCount_difference {ι : Type*} (J : Finset ι) (K : Nat) (d t : ι → Nat)
    (hd : ∀ j ∈ J, 2 ≤ d j) (n : Nat) (hn : 2 ≤ n) :
    rowCount J K d t n - rowCount J K d t (n - 1) =
      (if n ≤ K then 2 * (n : Int) + 1 else 0) +
      ∑ j ∈ J, ((if n + 1 ≤ d j then 2 * (n : Int) - 1 else 0) +
        (if n = d j then (t j : Int) else 0)) := by
  unfold rowCount
  rw [show smallRowCount K n + ∑ j ∈ J, largeRowCount (d j) (t j) n -
      (smallRowCount K (n - 1) + ∑ j ∈ J, largeRowCount (d j) (t j) (n - 1)) =
      (smallRowCount K n - smallRowCount K (n - 1)) +
      ((∑ j ∈ J, largeRowCount (d j) (t j) n) -
        ∑ j ∈ J, largeRowCount (d j) (t j) (n - 1)) by ring]
  rw [smallRowCount_difference K n (by omega), ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact largeRowCount_difference (d j) (t j) n (hd j hj) hn

/-- The increment expressed in the two statistics of the constructed pairs. -/
theorem rowCount_difference_statistics {ι : Type*} (J : Finset ι) (K : Nat)
    (d t : ι → Nat) (hd : ∀ j ∈ J, 2 ≤ d j) (n : Nat) (hn : 2 ≤ n) :
    rowCount J K d t n - rowCount J K d t (n - 1) =
      (if n ≤ K then 2 * (n : Int) + 1 else 0) +
      ((J.filter (fun j => n + 1 ≤ d j)).card : Int) * (2 * (n : Int) - 1) +
      ∑ j ∈ J.filter (fun j => n = d j), (t j : Int) := by
  rw [rowCount_difference J K d t hd n hn, Finset.sum_add_distrib]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- For rows bounded by N+1, no large-generator contribution changes after N+1. -/
theorem rowCount_tail_difference {ι : Type*} (J : Finset ι) (K N : Nat)
    (d t : ι → Nat) (hd : ∀ j ∈ J, 2 ≤ d j ∧ d j ≤ N + 1)
    (ht : ∀ j ∈ J, d j = N + 1 → t j = 0)
    (n : Nat) (hn : N + 1 ≤ n) (hn2 : 2 ≤ n) :
    rowCount J K d t n - rowCount J K d t (n - 1) =
      if n ≤ K then 2 * (n : Int) + 1 else 0 := by
  rw [rowCount_difference J K d t (fun j hj => (hd j hj).1) n hn2]
  suffices hh : (∑ j ∈ J, ((if n + 1 ≤ d j then 2 * (n : Int) - 1 else 0) +
      (if n = d j then (t j : Int) else 0))) = 0 by rw [hh, add_zero]
  apply Finset.sum_eq_zero
  intro j hj
  have hdb := (hd j hj).2
  rw [ite_eq_right (by omega : ¬ n + 1 ≤ d j), zero_add]
  by_cases he : n = d j
  · have ht' := ht j hj (by omega)
    rw [ite_eq_left he, ht']
    rfl
  · exact ite_eq_right he

end BuchweitzProfiles
