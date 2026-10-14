import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.DeriveFintype

namespace ASR312

/-- The three literal matrix entries. -/
inductive Entry where
  | minus | zero | plus
  deriving DecidableEq

instance : Fintype Entry := ⟨{.minus,.zero,.plus},by intro x; cases x <;> simp⟩

abbrev Rectangle (r k : ℕ) := Fin r → Fin k → Entry

def nonzeroEntries (l : List Entry) : List Entry := l.filter (· != .zero)

def Alternates (l : List Entry) : Prop := (nonzeroEntries l).IsChain (· ≠ ·)

def StartsPositive (l : List Entry) : Prop :=
  (nonzeroEntries l).head? = none ∨ (nonzeroEntries l).head? = some .plus

def EndsPositive (l : List Entry) : Prop :=
  (nonzeroEntries l).getLast? = none ∨ (nonzeroEntries l).getLast? = some .plus

def row {r k : ℕ} (A : Rectangle r k) (i : Fin r) : List Entry := List.ofFn (A i)
def col {r k : ℕ} (A : Rectangle r k) (j : Fin k) : List Entry := List.ofFn (fun i => A i j)

/-- The source's asymmetric row and column boundary conditions. -/
def IsASR {r k : ℕ} (A : Rectangle r k) : Prop :=
  (∀ i, Alternates (row A i) ∧ StartsPositive (row A i) ∧ EndsPositive (row A i)) ∧
  (∀ j, Alternates (col A j) ∧ StartsPositive (col A j))

/-- A square ASM has nonempty rows and columns, alternating with both ends positive. -/
def IsASM {n : ℕ} (A : Rectangle n n) : Prop :=
  IsASR A ∧ (∀ i, ∃ j, A i j ≠ .zero) ∧
    (∀ j, (∃ i, A i j ≠ .zero) ∧ EndsPositive (col A j))

def Avoids312 {r k : ℕ} (A : Rectangle r k) : Prop :=
  ¬∃ (i₁ i₂ i₃ : Fin r) (j₁ j₂ j₃ : Fin k),
    i₁ < i₂ ∧ i₂ < i₃ ∧ j₁ < j₂ ∧ j₂ < j₃ ∧
    A i₁ j₃ = .plus ∧ A i₂ j₁ = .plus ∧ A i₃ j₂ = .plus

/-- Existential extension to a square avoiding ASM, not internal avoidance alone. -/
def ExtendablyAvoids312 {r k : ℕ} (A : Rectangle r k) : Prop :=
  ∃ (n : ℕ) (hr : r ≤ n) (hk : k ≤ n) (B : Rectangle n n),
    IsASM B ∧ Avoids312 B ∧ ∀ i j, B (Fin.castLE hr i) (Fin.castLE hk j) = A i j

noncomputable def nonemptyRows {r k : ℕ} (A : Rectangle r k) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => ∃ j, A i j ≠ .zero)).card

noncomputable def S (r k d : ℕ) : ℕ := by
  classical
  exact Fintype.card {A : Rectangle r k //
    IsASR A ∧ nonemptyRows A = d ∧ ExtendablyAvoids312 A}

end ASR312
