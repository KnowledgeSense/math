import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

open scoped BigOperators Polynomial

theorem nonnegative_polynomial_root_multiplicity {p : ℝ[X]} (hp : p ≠ 0)
    (hn : ∀ x : ℝ, 0 < x → 0 ≤ p.eval x) {x : ℝ}
    (hx : 0 < x) (hroot : p.eval x = 0) : 2 ≤ p.rootMultiplicity x := by
  have hmin : IsLocalMin (fun y : ℝ => p.eval y) x := by
    change ∀ᶠ y in nhds x, p.eval x ≤ p.eval y
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [hroot]
    exact hn y hy
  have hder : p.derivative.eval x = 0 := hmin.hasDerivAt_eq_zero (p.hasDerivAt x)
  have hm : 1 < p.rootMultiplicity x :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hroot, hder⟩
  omega

theorem positive_root_multiplicity_sum {p : ℝ[X]} (hp : p ≠ 0)
    (hn : ∀ x : ℝ, 0 < x → 0 ≤ p.eval x) (s : Finset ℝ)
    (hs : ∀ x ∈ s, 0 < x ∧ p.eval x = 0) :
    2 * s.card ≤ p.natDegree := by
  classical
  have hsubset : s ⊆ p.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hs x hx).2)
  calc
    2 * s.card = ∑ x ∈ s, 2 := by simp [mul_comm]
    _ ≤ ∑ x ∈ s, p.roots.count x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Polynomial.count_roots]
      exact nonnegative_polynomial_root_multiplicity hp hn (hs x hx).1 (hs x hx).2
    _ ≤ ∑ x ∈ p.roots.toFinset, p.roots.count x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
    _ = p.roots.card := Multiset.toFinset_sum_count_eq _
    _ ≤ p.natDegree := Polynomial.card_roots' p

theorem positive_roots_and_zero_multiplicity_sum {p : ℝ[X]} (hp : p ≠ 0)
    (hn : ∀ x : ℝ, 0 < x → 0 ≤ p.eval x) (hzero : p.eval 0 = 0)
    (s : Finset ℝ) (hs : ∀ x ∈ s, 0 < x ∧ p.eval x = 0) :
    2 * s.card + 1 ≤ p.natDegree := by
  classical
  have h0 : (0 : ℝ) ∉ s := by
    intro h
    exact (lt_irrefl (0 : ℝ)) (hs 0 h).1
  have hsubset : insert (0 : ℝ) s ⊆ p.roots.toFinset := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hzero)
    · exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hs x hx).2)
  have hcount0 : 1 ≤ p.roots.count 0 := by
    rw [Polynomial.count_roots]
    exact Nat.succ_le_iff.mpr ((Polynomial.rootMultiplicity_pos hp).mpr hzero)
  have hcounts : 2 * s.card ≤ ∑ x ∈ s, p.roots.count x := by
    calc
      2 * s.card = ∑ x ∈ s, 2 := by simp [mul_comm]
      _ ≤ ∑ x ∈ s, p.roots.count x := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Polynomial.count_roots]
        exact nonnegative_polynomial_root_multiplicity hp hn (hs x hx).1 (hs x hx).2
  calc
    2 * s.card + 1 ≤ (∑ x ∈ s, p.roots.count x) + p.roots.count 0 :=
      Nat.add_le_add hcounts hcount0
    _ = ∑ x ∈ insert (0 : ℝ) s, p.roots.count x := by
      rw [Finset.sum_insert h0]
      omega
    _ ≤ ∑ x ∈ p.roots.toFinset, p.roots.count x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
    _ = p.roots.card := Multiset.toFinset_sum_count_eq _
    _ ≤ p.natDegree := Polynomial.card_roots' p

theorem quartic_positive_contacts {p : ℝ[X]} (hp : p ≠ 0)
    (hn : ∀ x : ℝ, 0 < x → 0 ≤ p.eval x) (hdeg : p.natDegree ≤ 4)
    (s : Finset ℝ) (hs : ∀ x ∈ s, 0 < x ∧ p.eval x = 0) :
    s.card ≤ 2 := by
  have h := positive_root_multiplicity_sum hp hn s hs
  omega

theorem quartic_two_positive_contacts_exclude_boundary {p : ℝ[X]} (hp : p ≠ 0)
    (hn : ∀ x : ℝ, 0 < x → 0 ≤ p.eval x) (hdeg : p.natDegree ≤ 4)
    (s : Finset ℝ) (hs : ∀ x ∈ s, 0 < x ∧ p.eval x = 0) (hc : s.card = 2) :
    p.eval 0 ≠ 0 ∧ p.natDegree = 4 := by
  have hmass := positive_root_multiplicity_sum hp hn s hs
  constructor
  · intro hz
    have h := positive_roots_and_zero_multiplicity_sum hp hn hz s hs
    omega
  · omega

noncomputable def positiveContacts (p : ℝ[X]) : Finset ℝ :=
  p.roots.toFinset.filter fun x => 0 < x

theorem quartic_contact_classification {p : ℝ[X]} (hp : p ≠ 0)
    (hn : ∀ x : ℝ, 0 < x → 0 ≤ p.eval x) (hdeg : p.natDegree ≤ 4) :
    (positiveContacts p).card + (if p.eval 0 = 0 then 1 else 0) +
      (if p.natDegree < 4 then 1 else 0) ≤ 2 ∨
    ((positiveContacts p).card = 1 ∧ p.eval 0 = 0 ∧ p.natDegree < 4) := by
  classical
  have hs : ∀ x ∈ positiveContacts p, 0 < x ∧ p.eval x = 0 := by
    intro x hx
    obtain ⟨hroot, hxpos⟩ := Finset.mem_filter.mp hx
    exact ⟨hxpos, (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp hroot)⟩
  have hc := quartic_positive_contacts hp hn hdeg (positiveContacts p) hs
  by_cases htwo : (positiveContacts p).card = 2
  · have hb := quartic_two_positive_contacts_exclude_boundary hp hn hdeg
      (positiveContacts p) hs htwo
    left
    simp [htwo, hb.1, hb.2]
  · by_cases hzero : p.eval 0 = 0
    · by_cases hinfinity : p.natDegree < 4
      · by_cases hone : (positiveContacts p).card = 1
        · exact Or.inr ⟨hone, hzero, hinfinity⟩
        · left
          simp only [hzero, hinfinity, ite_true]
          omega
      · left
        simp only [hzero, hinfinity, ite_true, ite_false]
        omega
    · left
      split_ifs <;> omega

end ResearchMain.DiagonalSchatten
