import MainTheorems.PreorderGamma.SimplicialRealization.DiagonalNormalForm

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]
variable {d s : Option E → ℕ}

def originalDiagonalValue (p : NaturalTransport augmentedRelation d s) : Option E → ℕ
  | none => 0
  | some i => p.flow (some i) (some i)

def originalDiagonalRemoval (p : NaturalTransport augmentedRelation d s)
    (a b : Option E) : ℕ := if a = b then originalDiagonalValue p a else 0

theorem originalDiagonalRemoval_le (p : NaturalTransport augmentedRelation d s)
    (a b : Option E) : originalDiagonalRemoval p a b ≤ p.flow a b := by
  by_cases h : a = b
  · subst b
    cases a <;> simp [originalDiagonalRemoval, originalDiagonalValue]
  · simp [originalDiagonalRemoval, h]

theorem originalDiagonalRemoval_row (p : NaturalTransport augmentedRelation d s)
    (a : Option E) : (∑ b, originalDiagonalRemoval p a b) = originalDiagonalValue p a := by
  classical
  calc
    _ = originalDiagonalRemoval p a a := by
      apply Finset.sum_eq_single a
      · intro b hb hba
        simp [originalDiagonalRemoval, Ne.symm hba]
      · simp
    _ = _ := by simp [originalDiagonalRemoval]

theorem originalDiagonalRemoval_column (p : NaturalTransport augmentedRelation d s)
    (b : Option E) : (∑ a, originalDiagonalRemoval p a b) = originalDiagonalValue p b := by
  classical
  calc
    _ = originalDiagonalRemoval p b b := by
      apply Finset.sum_eq_single b
      · intro a ha hab
        simp [originalDiagonalRemoval, hab]
      · simp
    _ = _ := by simp [originalDiagonalRemoval]

def stripOriginalDiagonal (p : NaturalTransport augmentedRelation d s) :
    NaturalTransport augmentedRelation
      (fun a => d a - originalDiagonalValue p a)
      (fun b => s b - originalDiagonalValue p b) where
  flow := fun a b => p.flow a b - originalDiagonalRemoval p a b
  supported := by
    intro a b hab
    rw [p.supported a b hab]
    exact Nat.zero_sub _
  row_sum := by
    intro a
    have heq : (∑ b, (p.flow a b - originalDiagonalRemoval p a b)) +
        originalDiagonalValue p a = d a := by
      rw [← originalDiagonalRemoval_row p a, ← Finset.sum_add_distrib]
      exact (Finset.sum_congr rfl (fun b _ =>
        Nat.sub_add_cancel (originalDiagonalRemoval_le p a b))).trans (p.row_sum a)
    omega
  column_sum := by
    intro b
    have heq : (∑ a, (p.flow a b - originalDiagonalRemoval p a b)) +
        originalDiagonalValue p b = s b := by
      rw [← originalDiagonalRemoval_column p b, ← Finset.sum_add_distrib]
      exact (Finset.sum_congr rfl (fun a _ =>
        Nat.sub_add_cancel (originalDiagonalRemoval_le p a b))).trans (p.column_sum b)
    omega

@[simp] theorem stripOriginalDiagonal_none_none
    (p : NaturalTransport augmentedRelation d s) :
    (stripOriginalDiagonal p).flow none none = p.flow none none := by
  simp [stripOriginalDiagonal, originalDiagonalRemoval, originalDiagonalValue]

@[simp] theorem stripOriginalDiagonal_diagonal
    (p : NaturalTransport augmentedRelation d s) (i : E) :
    (stripOriginalDiagonal p).flow (some i) (some i) = 0 := by
  simp [stripOriginalDiagonal, originalDiagonalRemoval, originalDiagonalValue]

theorem stripOriginalDiagonal_offDiagonal
    (p : NaturalTransport augmentedRelation d s) (a b : Option E) (hab : a ≠ b) :
    (stripOriginalDiagonal p).flow a b = p.flow a b := by
  simp [stripOriginalDiagonal, originalDiagonalRemoval, hab]

omit [DecidableEq E] in
theorem normalForm_stripped_row (p : NaturalTransport augmentedRelation d s)
    (hp : ∀ i : E, p.flow (some i) (some i) = min (d (some i)) (s (some i)))
    (i : E) :
    d (some i) - originalDiagonalValue p (some i) =
      ((d (some i) : ℤ) - (s (some i) : ℤ)).toNat := by
  simp only [originalDiagonalValue, hp i]
  omega

omit [DecidableEq E] in
theorem normalForm_stripped_column (p : NaturalTransport augmentedRelation d s)
    (hp : ∀ i : E, p.flow (some i) (some i) = min (d (some i)) (s (some i)))
    (i : E) :
    s (some i) - originalDiagonalValue p (some i) =
      ((s (some i) : ℤ) - (d (some i) : ℤ)).toNat := by
  simp only [originalDiagonalValue, hp i]
  omega

end ResearchMain.PreorderGamma.SimplicialRealization
