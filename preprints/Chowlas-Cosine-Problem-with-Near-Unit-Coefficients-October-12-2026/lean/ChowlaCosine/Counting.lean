import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# The support counting lemma for Chowla's cosine problem

This file proves the counting input of the 12 October 2026 release directly for
finite subsets of the integers. In particular, no counting identity is assumed.
-/

namespace ChowlaCosine

open Finset
open scoped BigOperators

/-- The asymmetric part of the intersection with the translate by `t`. -/
def B (A : Finset ℤ) (t : ℤ) : Finset ℤ :=
  A.filter (fun m => m - t ∈ A ∧ m + t ∉ A)

/-- The part of the intersection with both neighbouring translates. -/
def C (A : Finset ℤ) (t : ℤ) : Finset ℤ :=
  A.filter (fun m => m - t ∈ A ∧ m + t ∈ A)

/-- The number of ordered additive triples used in the paper. -/
def T (A : Finset ℤ) : ℕ :=
  ∑ t ∈ A, (A.filter (fun m => m - t ∈ A)).card

/-- The total asymmetric contribution. -/
def Btot (A : Finset ℤ) : ℕ := ∑ t ∈ A, (B A t).card

/-- The total symmetric contribution. -/
def Ctot (A : Finset ℤ) : ℕ := ∑ t ∈ A, (C A t).card

/-- Positive elements of the support. -/
def positivePart (A : Finset ℤ) : Finset ℤ := A.filter (0 < ·)

/-- A natural-valued indicator, useful for finite double counting. -/
def supportIndicator (A : Finset ℤ) (m : ℤ) : ℕ := if m ∈ A then 1 else 0

/-- Ordered positive pairs whose sum belongs to the support. -/
def positiveSumPairs (A : Finset ℤ) : Finset (ℤ × ℤ) :=
  (positivePart A ×ˢ positivePart A).filter (fun p => p.1 + p.2 ∈ A)

/-- Ordered positive pairs whose difference belongs to the support. -/
def positiveDifferencePairs (A : Finset ℤ) : Finset (ℤ × ℤ) :=
  (positivePart A ×ˢ positivePart A).filter (fun p => p.1 - p.2 ∈ A)

@[simp] theorem mem_positivePart {A : Finset ℤ} {m : ℤ} :
    m ∈ positivePart A ↔ m ∈ A ∧ 0 < m := by
  simp [positivePart]

private theorem neg_mem_iff {A : Finset ℤ}
    (hA : ∀ m ∈ A, -m ∈ A) (m : ℤ) : -m ∈ A ↔ m ∈ A := by
  constructor
  · intro h
    simpa using hA (-m) h
  · exact hA m

private theorem indicator_neg {A : Finset ℤ}
    (hA : ∀ m ∈ A, -m ∈ A) (m : ℤ) :
    supportIndicator A (-m) = supportIndicator A m := by
  simp [supportIndicator, neg_mem_iff hA]

/-- Splitting a symmetric support into its positive and negative elements. -/
theorem sum_eq_positive_add_negative {A : Finset ℤ}
    (hA : ∀ m ∈ A, -m ∈ A) (h0 : 0 ∉ A) (f : ℤ → ℕ) :
    ∑ m ∈ A, f m = ∑ m ∈ positivePart A, (f m + f (-m)) := by
  have hn : ∑ m ∈ A.filter (fun m => ¬ 0 < m), f m =
      ∑ m ∈ positivePart A, f (-m) := by
    apply Finset.sum_bij (fun m _ => -m)
    · intro m hm
      obtain ⟨hm, hm0⟩ := Finset.mem_filter.mp hm
      have hmne : m ≠ 0 := fun h => h0 (h ▸ hm)
      exact mem_positivePart.mpr ⟨hA m hm, by omega⟩
    · intro m _ n _ h
      simpa using h
    · intro n hn
      obtain ⟨hn, hn0⟩ := mem_positivePart.mp hn
      exact ⟨-n, Finset.mem_filter.mpr ⟨hA n hn, by omega⟩, by simp⟩
    · intro m _
      simp
  rw [← Finset.sum_filter_add_sum_filter_not A (fun m => 0 < m) f, hn]
  simp [positivePart, Finset.sum_add_distrib]

private theorem double_sum_signs {A : Finset ℤ}
    (hA : ∀ m ∈ A, -m ∈ A) (h0 : 0 ∉ A) (f : ℤ → ℤ → ℕ) :
    (∑ m ∈ A, ∑ t ∈ A, f m t) =
      ∑ u ∈ positivePart A, ∑ v ∈ positivePart A,
        (f u v + f u (-v) + f (-u) v + f (-u) (-v)) := by
  rw [sum_eq_positive_add_negative hA h0]
  apply Finset.sum_congr rfl
  intro u hu
  rw [sum_eq_positive_add_negative hA h0,
    sum_eq_positive_add_negative hA h0, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  omega

/-- The two support pieces partition every translated intersection. -/
theorem T_eq_Btot_add_Ctot (A : Finset ℤ) : T A = Btot A + Ctot A := by
  unfold T Btot Ctot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [B, C, Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hd : m - t ∈ A <;> by_cases hp : m + t ∈ A <;> simp [hd, hp]

/-- The bijection `(u,v) ↦ (v,u-v)` for `u>v`. -/
private theorem positive_difference_gt_card (A : Finset ℤ) :
    ((positiveDifferencePairs A).filter (fun p => p.2 < p.1)).card =
      (positiveSumPairs A).card := by
  refine Finset.card_bij' (fun p _ => (p.2, p.1 - p.2))
    (fun p _ => (p.1 + p.2, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨u,v⟩ h
    simp only [positiveDifferencePairs, positiveSumPairs, Finset.mem_filter,
      Finset.mem_product, mem_positivePart] at h ⊢
    obtain ⟨⟨⟨⟨hu, hu0⟩, ⟨hv, hv0⟩⟩, hd⟩, hlt⟩ := h
    exact ⟨⟨⟨hv, hv0⟩, ⟨hd, by omega⟩⟩, by simpa using hu⟩
  · rintro ⟨u,v⟩ h
    simp only [positiveDifferencePairs, positiveSumPairs, Finset.mem_filter,
      Finset.mem_product, mem_positivePart] at h ⊢
    obtain ⟨⟨⟨hu, hu0⟩, ⟨hv, hv0⟩⟩, hs⟩ := h
    exact ⟨⟨⟨⟨hs, by omega⟩, ⟨hu, hu0⟩⟩, by simpa using hv⟩, by omega⟩
  · rintro ⟨u,v⟩ h
    simp
  · rintro ⟨u,v⟩ h
    simp

/-- The bijection `(u,v) ↦ (u,v-u)` for `u<v`. -/
private theorem positive_difference_le_card {A : Finset ℤ}
    (hA : ∀ m ∈ A, -m ∈ A) (h0 : 0 ∉ A) :
    ((positiveDifferencePairs A).filter (fun p => ¬ p.2 < p.1)).card =
      (positiveSumPairs A).card := by
  refine Finset.card_bij' (fun p _ => (p.1, p.2 - p.1))
    (fun p _ => (p.1, p.1 + p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨u,v⟩ h
    simp only [positiveDifferencePairs, positiveSumPairs, Finset.mem_filter,
      Finset.mem_product, mem_positivePart] at h ⊢
    obtain ⟨⟨⟨⟨hu, hu0⟩, ⟨hv, hv0⟩⟩, hd⟩, hlt⟩ := h
    have hne : u ≠ v := by
      intro heq
      subst v
      exact h0 (by simpa using hd)
    have hd' : v - u ∈ A := by simpa using hA (u-v) hd
    exact ⟨⟨⟨hu, hu0⟩, ⟨hd', by omega⟩⟩, by simpa using hv⟩
  · rintro ⟨u,v⟩ h
    simp only [positiveDifferencePairs, positiveSumPairs, Finset.mem_filter,
      Finset.mem_product, mem_positivePart] at h ⊢
    obtain ⟨⟨⟨hu, hu0⟩, ⟨hv, hv0⟩⟩, hs⟩ := h
    exact ⟨⟨⟨⟨hu, hu0⟩, ⟨hs, by omega⟩⟩, by simpa using hA v hv⟩, by omega⟩
  · rintro ⟨u,v⟩ h
    simp
  · rintro ⟨u,v⟩ h
    simp

/-- Shankar's elementary positive-pair identity, proved by two bijections. -/
theorem positive_difference_card {A : Finset ℤ}
    (hA : ∀ m ∈ A, -m ∈ A) (h0 : 0 ∉ A) :
    (positiveDifferencePairs A).card = 2 * (positiveSumPairs A).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := positiveDifferencePairs A) (fun p : ℤ × ℤ => p.2 < p.1)
  rw [positive_difference_gt_card, positive_difference_le_card hA h0] at h
  omega

private theorem positive_sum_card (A : Finset ℤ) :
    (positiveSumPairs A).card = ∑ u ∈ positivePart A, ∑ v ∈ positivePart A,
      supportIndicator A (u+v) := by
  simp only [positiveSumPairs, Finset.card_filter, Finset.sum_product, supportIndicator]

private theorem positive_difference_card_sum (A : Finset ℤ) :
    (positiveDifferencePairs A).card = ∑ u ∈ positivePart A, ∑ v ∈ positivePart A,
      supportIndicator A (u-v) := by
  simp only [positiveDifferencePairs, Finset.card_filter, Finset.sum_product, supportIndicator]

/-- The total number of additive triples is six times the positive sum count. -/
theorem T_eq_six_positive_sum_pairs {A : Finset ℤ}
    (hA : ∀ m ∈ A, -m ∈ A) (h0 : 0 ∉ A) :
    T A = 6 * (positiveSumPairs A).card := by
  have hs : T A = 2 * ((positiveDifferencePairs A).card +
      (positiveSumPairs A).card) := by
    unfold T
    simp only [Finset.card_filter]
    change (∑ t ∈ A, ∑ m ∈ A, supportIndicator A (m-t)) = _
    rw [double_sum_signs hA h0]
    rw [positive_sum_card, positive_difference_card_sum, two_mul]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    have hd : supportIndicator A (v-u) = supportIndicator A (u-v) := by
      simpa using indicator_neg hA (u-v)
    have hs : supportIndicator A (-v-u) = supportIndicator A (u+v) := by
      convert indicator_neg hA (u+v) using 1
      congr 1
      omega
    have hn : supportIndicator A (-v- -u) = supportIndicator A (u-v) := by
      congr 1
      omega
    have hp : supportIndicator A (v- -u) = supportIndicator A (u+v) := by
      congr 1
      omega
    rw [hd, hs, hn, hp]
    omega
  rw [positive_difference_card hA h0] at hs
  omega

/-- At most four signed versions of each positive sum pair contribute to `Ctot`. -/
theorem Ctot_le_four_positive_sum_pairs {A : Finset ℤ}
    (hA : ∀ m ∈ A, -m ∈ A) (h0 : 0 ∉ A) :
    Ctot A ≤ 4 * (positiveSumPairs A).card := by
  unfold Ctot C
  simp only [Finset.card_filter]
  rw [double_sum_signs hA h0, positive_sum_card]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro v hv
  have hd : v-u ∈ A ↔ u-v ∈ A := by
    have heq : v-u = -(u-v) := by omega
    rw [heq]
    exact neg_mem_iff hA (u-v)
  have hs : -v-u ∈ A ↔ u+v ∈ A := by
    have heq : -v-u = -(u+v) := by omega
    rw [heq]
    exact neg_mem_iff hA (u+v)
  have hn : -v- -u = u-v := by omega
  have hp : v- -u = u+v := by omega
  have hq : -v+u = u-v := by omega
  have hr : -v+ -u = -v-u := by omega
  simp only [← sub_eq_add_neg, hn, hp, hq, hr, add_comm v u, hd, hs, supportIndicator]
  by_cases hsum : u+v ∈ A <;> by_cases hdiff : u-v ∈ A <;>
    simp [hsum, hdiff]

/-- Shankar's counting lemma, in a division-free natural-number form. -/
theorem shankar_counting {A : Finset ℤ}
    (hA : ∀ m ∈ A, -m ∈ A) (h0 : 0 ∉ A) :
    T A ≤ 3 * Btot A := by
  have hT := T_eq_six_positive_sum_pairs hA h0
  have hC := Ctot_le_four_positive_sum_pairs hA h0
  have hBC := T_eq_Btot_add_Ctot A
  omega

/-- The aggregate error estimate used in the proof of the main theorem. -/
theorem Ctot_le_two_Btot {A : Finset ℤ}
    (hA : ∀ m ∈ A, -m ∈ A) (h0 : 0 ∉ A) :
    Ctot A ≤ 2 * Btot A := by
  have h := shankar_counting hA h0
  rw [T_eq_Btot_add_Ctot] at h
  omega

/-- The sum formulation, with the actual finite sets `B_t` and `C_t`. -/
theorem sum_card_C_le_two_sum_card_B {A : Finset ℤ}
    (hA : ∀ m ∈ A, -m ∈ A) (h0 : 0 ∉ A) :
    (∑ t ∈ A, (C A t).card) ≤ 2 * ∑ t ∈ A, (B A t).card :=
  Ctot_le_two_Btot hA h0

end ChowlaCosine
