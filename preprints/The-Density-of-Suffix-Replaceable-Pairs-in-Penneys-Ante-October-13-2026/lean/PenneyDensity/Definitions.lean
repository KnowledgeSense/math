import Mathlib.Data.List.Infix
import Mathlib.Data.List.OfFn
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

noncomputable section
namespace PenneyDensity

abbrev Word := List Bool

/-- Literal stopped contexts: the appended target occurs exactly once, at
its final suffix, and the competing target never occurs. -/
def StoppedLanguage (v w : Word) : Set Word :=
  {u | (∀ l r : Word, u++v=l++v++r → l=u ∧ r=[]) ∧ ¬w.IsInfix (u++v)}

def PropertyR (v w : Word) : Prop := StoppedLanguage v w=StoppedLanguage w v

abbrev WordOfLength (n : ℕ) := Fin n → Bool

def toWord {n : ℕ} (v : WordOfLength n) : Word := List.ofFn v


/-- Exact whole-pair density, with the literal diagonal convention. -/
def density (n : ℕ) : ℝ := by
  classical
  exact (Nat.card {p : WordOfLength n × WordOfLength n //
    PropertyR (toWord p.1) (toWord p.2)} : ℝ) / 4^n

def distinctDensity (n : ℕ) : ℝ := by
  classical
  exact (Nat.card {p : WordOfLength n × WordOfLength n //
    p.1≠p.2 ∧ PropertyR (toWord p.1) (toWord p.2)} : ℝ) / 4^n

def properOverlap (a t : Word) (k : ℕ) : Prop :=
  0<k ∧ k<a.length ∧ a.drop (a.length-k)=t.take k

/-- The literal forbidden suffix generators in the source criterion. -/
def forbidden (v w t : Word) : Set Word :=
  {b | ∃ a, (a=v ∨ a=w) ∧ ∃ k, properOverlap a t k ∧ b=a.take (a.length-k)}

def Avoids (v w u : Word) : Prop := ¬v.IsInfix u ∧ ¬w.IsInfix u

 theorem stoppedLanguage_diagonal (v : Word) : StoppedLanguage v v=∅ := by
  ext u
  simp only [StoppedLanguage,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
  rintro ⟨_,hh⟩
  exact hh ⟨u,[],by simp⟩

 theorem diagonal_propertyR (v : Word) : PropertyR v v := rfl

 theorem toWord_length {n : ℕ} (v : WordOfLength n) : (toWord v).length=n := by
  exact List.length_ofFn

end PenneyDensity
