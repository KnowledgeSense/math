import MainTheorems.PreorderGamma.TransportOptimality
import MainTheorems.PreorderGamma.RootPolytope
import Mathlib.Data.Finset.Max

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]
variable {d s : Option E → ℕ}

theorem transportUnitEdge_row_sum {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] (a₀ : L) (b₀ : R) (a : L) :
    (∑ b, transportUnitEdge a₀ b₀ a b) = if a = a₀ then 1 else 0 := by
  classical
  by_cases h : a = a₀
  · subst a
    simp [transportUnitEdge]
  · simp [transportUnitEdge, h]

theorem transportUnitEdge_column_sum {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] (a₀ : L) (b₀ : R) (b : R) :
    (∑ a, transportUnitEdge a₀ b₀ a b) = if b = b₀ then 1 else 0 := by
  classical
  by_cases h : b = b₀
  · subst b
    simp [transportUnitEdge]
  · simp [transportUnitEdge, h]

theorem original_offDiagonal_entries
    (p : NaturalTransport augmentedRelation d s) (i : E)
    (hi : p.flow (some i) (some i) < min (d (some i)) (s (some i))) :
    (∃ a : Option E, a ≠ some i ∧ 0 < p.flow a (some i)) ∧
      ∃ b : Option E, b ≠ some i ∧ 0 < p.flow (some i) b := by
  classical
  constructor
  · by_contra h
    have hz : ∀ a : Option E, a ≠ some i → p.flow a (some i) = 0 := by
      intro a ha
      by_contra hzero
      exact h ⟨a, ha, Nat.pos_of_ne_zero hzero⟩
    have heq : (∑ a, p.flow a (some i)) = p.flow (some i) (some i) := by
      apply Finset.sum_eq_single (some i)
      · intro a ha hne
        exact hz a hne
      · simp
    rw [p.column_sum] at heq
    have hbound := min_le_right (d (some i)) (s (some i))
    omega
  · by_contra h
    have hz : ∀ b : Option E, b ≠ some i → p.flow (some i) b = 0 := by
      intro b hb
      by_contra hzero
      exact h ⟨b, hb, Nat.pos_of_ne_zero hzero⟩
    have heq : (∑ b, p.flow (some i) b) = p.flow (some i) (some i) := by
      apply Finset.sum_eq_single (some i)
      · intro b hb hne
        exact hz b hne
      · simp
    rw [p.row_sum] at heq
    have hbound := min_le_left (d (some i)) (s (some i))
    omega

omit [Fintype E] [DecidableEq E] in
theorem original_shortcut_allowed (i : E) (a b : Option E)
    (ha : augmentedRelation a (some i)) (hb : augmentedRelation (some i) b) :
    augmentedRelation a b := by
  cases a with
  | none => trivial
  | some a =>
    cases b with
    | none => trivial
    | some b => exact le_trans hb ha

noncomputable def diagonalShortcut (p : NaturalTransport augmentedRelation d s)
    (i : E) (a b : Option E) (hai : a ≠ some i) (hbi : b ≠ some i)
    (ha : 0 < p.flow a (some i)) (hb : 0 < p.flow (some i) b) : FeasibleTransfer p := by
  classical
  have har : augmentedRelation a (some i) := by
    by_contra h
    have hz := p.supported a (some i) h
    omega
  have hbr : augmentedRelation (some i) b := by
    by_contra h
    have hz := p.supported (some i) b h
    omega
  have hab := original_shortcut_allowed i a b har hbr
  refine
    { increase := fun x y => transportUnitEdge a b x y + transportUnitEdge (some i) (some i) x y
      decrease := fun x y => transportUnitEdge a (some i) x y + transportUnitEdge (some i) b x y
      increase_supported := ?_
      decrease_le := ?_
      row_balance := ?_
      column_balance := ?_ }
  · intro x y hxy
    have h₁ : ¬(x = a ∧ y = b) := by
      rintro ⟨rfl, rfl⟩
      exact hxy hab
    have h₂ : ¬(x = some i ∧ y = some i) := by
      rintro ⟨rfl, rfl⟩
      exact hxy (show augmentedRelation (some i) (some i) from le_rfl)
    simp [transportUnitEdge, h₁, h₂]
  · intro x y
    by_cases h₁ : x = a ∧ y = some i
    · have h₂ : ¬(x = some i ∧ y = b) := by
        rintro ⟨hxi, hyb⟩
        exact hai (h₁.1.symm.trans hxi)
      simp only [transportUnitEdge, ite_eq_left h₁, ite_eq_right h₂, add_zero]
      simpa only [h₁.1, h₁.2] using Nat.succ_le_of_lt ha
    · by_cases h₂ : x = some i ∧ y = b
      · simp only [transportUnitEdge, ite_eq_right h₁, ite_eq_left h₂, zero_add]
        simpa only [h₂.1, h₂.2] using Nat.succ_le_of_lt hb
      · simp [transportUnitEdge, h₁, h₂]
  · intro x
    simp only [Finset.sum_add_distrib, transportUnitEdge_row_sum]
  · intro y
    simp only [Finset.sum_add_distrib, transportUnitEdge_column_sum]
    exact Nat.add_comm _ _

theorem diagonalShortcut_decrease_diagonal (p : NaturalTransport augmentedRelation d s)
    (i : E) (a b : Option E) (hai : a ≠ some i) (hbi : b ≠ some i)
    (ha : 0 < p.flow a (some i)) (hb : 0 < p.flow (some i) b) (j : E) :
    (diagonalShortcut p i a b hai hbi ha hb).decrease (some j) (some j) = 0 := by
  classical
  have h₁ : ¬(some j = a ∧ some j = some i) := by
    rintro ⟨hja, hji⟩
    exact hai (hja.symm.trans hji)
  have h₂ : ¬(some j = some i ∧ some j = b) := by
    rintro ⟨hji, hjb⟩
    exact hbi (hjb.symm.trans hji)
  simp only [diagonalShortcut, transportUnitEdge, ite_eq_right h₁, ite_eq_right h₂, add_zero]

noncomputable def originalDiagonalMass (p : NaturalTransport augmentedRelation d s) : ℕ :=
  ∑ i : E, p.flow (some i) (some i)

theorem diagonalShortcut_mass_lt (p : NaturalTransport augmentedRelation d s)
    (i : E) (a b : Option E) (hai : a ≠ some i) (hbi : b ≠ some i)
    (ha : 0 < p.flow a (some i)) (hb : 0 < p.flow (some i) b) :
    originalDiagonalMass p <
      originalDiagonalMass ((diagonalShortcut p i a b hai hbi ha hb).perturb p) := by
  classical
  let t := diagonalShortcut p i a b hai hbi ha hb
  have hdiag : ∀ j : E, p.flow (some j) (some j) ≤ (t.perturb p).flow (some j) (some j) := by
    intro j
    have h := t.perturb_entry_balance p (some j) (some j)
    have hz := diagonalShortcut_decrease_diagonal p i a b hai hbi ha hb j
    change t.decrease (some j) (some j) = 0 at hz
    rw [hz, Nat.add_zero] at h
    omega
  have hstrict : p.flow (some i) (some i) < (t.perturb p).flow (some i) (some i) := by
    have h := t.perturb_entry_balance p (some i) (some i)
    have hz := diagonalShortcut_decrease_diagonal p i a b hai hbi ha hb i
    have hone : t.increase (some i) (some i) = 1 := by
      simp [t, diagonalShortcut, transportUnitEdge, Ne.symm hai]
    change t.decrease (some i) (some i) = 0 at hz
    rw [hz, Nat.add_zero, hone] at h
    omega
  exact Finset.sum_lt_sum (fun j hj => hdiag j) ⟨i, Finset.mem_univ _, hstrict⟩

theorem exists_originalDiagonal_normalForm
    (p : NaturalTransport augmentedRelation d s) :
    ∃ q : NaturalTransport augmentedRelation d s,
      ∀ i : E, q.flow (some i) (some i) = min (d (some i)) (s (some i)) := by
  classical
  let : Nonempty (NaturalTransport augmentedRelation d s) := ⟨p⟩
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image Finset.univ
    (originalDiagonalMass (d := d) (s := s)) Finset.univ_nonempty
  refine ⟨q, ?_⟩
  intro i
  have hrow : q.flow (some i) (some i) ≤ d (some i) := by
    rw [← q.row_sum (some i)]
    exact Finset.single_le_sum (fun b hb => Nat.zero_le _) (Finset.mem_univ _)
  have hcol := q.entry_le (some i) (some i)
  have hbound := le_min hrow hcol
  by_contra hne
  have hi : q.flow (some i) (some i) < min (d (some i)) (s (some i)) :=
    lt_of_le_of_ne hbound hne
  obtain ⟨⟨a, hai, ha⟩, b, hbi, hb⟩ := original_offDiagonal_entries q i hi
  have hlt := diagonalShortcut_mass_lt q i a b hai hbi ha hb
  have hle := hmax ((diagonalShortcut q i a b hai hbi ha hb).perturb q)
    (Finset.mem_univ _)
  omega

end ResearchMain.PreorderGamma.SimplicialRealization
