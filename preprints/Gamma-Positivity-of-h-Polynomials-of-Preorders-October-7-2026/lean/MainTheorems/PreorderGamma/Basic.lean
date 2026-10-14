import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [Preorder E]

def IsIdeal (s : Finset E) : Prop :=
  ∀ ⦃a b : E⦄, b ∈ s → a ≤ b → a ∈ s

noncomputable def downward (s : Finset E) : Finset E := by
  classical
  exact Finset.univ.filter fun a => ∃ b ∈ s, a ≤ b

noncomputable def neighborhood (z s : Finset E) : Finset E := by
  classical
  exact z.filter fun a => ∃ b ∈ s, a ≤ b

noncomputable def zeroSet (x : E → ℕ) : Finset E := by
  classical
  exact Finset.univ.filter fun a => x a = 0

noncomputable def highSet (x : E → ℕ) : Finset E := by
  classical
  exact Finset.univ.filter fun a => 2 ≤ x a

def IsLatticePoint (x : E → ℕ) : Prop :=
  ∀ s : Finset E, IsIdeal s → ∑ a ∈ s, x a ≤ s.card

def SurplusHall (x : E → ℕ) : Prop :=
  ∀ s : Finset E, s ⊆ highSet x →
    ∑ a ∈ s, (x a - 1) ≤ (neighborhood (zeroSet x) s).card

@[simp] theorem mem_downward {a : E} {s : Finset E} :
    a ∈ downward s ↔ ∃ b ∈ s, a ≤ b := by
  classical
  simp [downward]

omit [Fintype E] in
@[simp] theorem mem_neighborhood {a : E} {z s : Finset E} :
    a ∈ neighborhood z s ↔ a ∈ z ∧ ∃ b ∈ s, a ≤ b := by
  classical
  simp [neighborhood]

omit [Preorder E] in
@[simp] theorem mem_zeroSet {a : E} {x : E → ℕ} :
    a ∈ zeroSet x ↔ x a = 0 := by
  classical
  simp [zeroSet]

omit [Preorder E] in
@[simp] theorem mem_highSet {a : E} {x : E → ℕ} :
    a ∈ highSet x ↔ 2 ≤ x a := by
  classical
  simp [highSet]

theorem subset_downward (s : Finset E) : s ⊆ downward s := by
  intro a ha
  exact mem_downward.mpr ⟨a, ha, le_rfl⟩

theorem downward_isIdeal (s : Finset E) : IsIdeal (downward s) := by
  intro a b hb hab
  obtain ⟨c, hc, hbc⟩ := mem_downward.mp hb
  exact mem_downward.mpr ⟨c, hc, hab.trans hbc⟩

theorem downward_eq_of_isIdeal {s : Finset E} (hs : IsIdeal s) : downward s = s := by
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨b, hb, hab⟩ := mem_downward.mp ha
    exact hs hb hab
  · exact subset_downward s

omit [Fintype E] [Preorder E] in
theorem zero_surplus_identity (x : E → ℕ) (s : Finset E) :
    (∑ a ∈ s, x a) + (s.filter fun a => x a = 0).card =
      s.card + ∑ a ∈ s, (x a - 1) := by
  classical
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  calc
    ∑ a ∈ s, (x a + if x a = 0 then 1 else 0) =
        ∑ a ∈ s, (1 + (x a - 1)) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : x a = 0
      · simp [h]
      · simp [h]
        omega
    _ = s.card + ∑ a ∈ s, (x a - 1) := by
      simp [Finset.sum_add_distrib]

omit [Fintype E] [Preorder E] in
theorem lattice_inequality_iff_surplus (x : E → ℕ) (s : Finset E) :
    (∑ a ∈ s, x a ≤ s.card) ↔
      ∑ a ∈ s, (x a - 1) ≤ (s.filter fun a => x a = 0).card := by
  have h := zero_surplus_identity x s
  omega

omit [Fintype E] [Preorder E] in
theorem sum_high_filter (x : E → ℕ) (s : Finset E) :
    (∑ a ∈ s.filter (fun a => 2 ≤ x a), (x a - 1)) =
      ∑ a ∈ s, (x a - 1) := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a ha hna
  have h : ¬ 2 ≤ x a := by
    intro h
    exact hna (Finset.mem_filter.mpr ⟨ha, h⟩)
  omega

theorem lattice_coordinate_bound {x : E → ℕ} (hx : IsLatticePoint x) (a : E) :
    x a ≤ Fintype.card E := by
  have hsum := hx Finset.univ (by intro b c hc hbc; exact Finset.mem_univ b)
  have ha : x a ≤ ∑ b : E, x b :=
    Finset.single_le_sum (fun b hb => Nat.zero_le (x b)) (Finset.mem_univ a)
  simpa using ha.trans hsum

noncomputable def latticePoints : Finset (E → Fin (Fintype.card E + 1)) := by
  classical
  exact Finset.univ.filter fun x => IsLatticePoint fun a => (x a).val

noncomputable def supportPolynomial : Polynomial ℕ := by
  classical
  exact ∑ x ∈ latticePoints (E := E),
    Polynomial.X ^ (Finset.univ.filter fun a => 0 < (x a).val).card

end ResearchMain.PreorderGamma
