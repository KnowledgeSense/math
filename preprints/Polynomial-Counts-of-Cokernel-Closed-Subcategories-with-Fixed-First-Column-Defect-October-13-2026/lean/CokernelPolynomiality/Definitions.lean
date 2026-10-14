import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

namespace CokernelPolynomiality

/-- The literal triangular point set of the Mazorchuk–Xu enumeration. -/
def triangle (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n+1)).product (Finset.range (n+1))).filter (fun p => p.1 ≤ p.2)

/-- The source's three-input closure rule. Inputs may repeat. -/
def IsClosed (Y : Finset (ℕ × ℕ)) : Prop :=
  ∀ a b c d e f : ℕ, (a,b) ∈ Y → (c,d) ∈ Y → (e,f) ∈ Y →
    a ≤ c → c ≤ b → b ≤ d → a ≤ e → e ≤ b → b ≤ f →
    (max c e, max d f) ∈ Y ∧ (b < min d f → (b+1,min d f) ∈ Y)

noncomputable def firstColumnSize (Y : Finset (ℕ × ℕ)) : ℕ :=
  (Y.filter (fun p => p.1 = 0)).card

/-- Count the original closed subsets with exactly k first-column points. -/
noncomputable def r (n k : ℕ) : ℕ := by
  classical
  exact ((triangle n).powerset.filter
    (fun Y => IsClosed Y ∧ firstColumnSize Y = k)).card

/-- Two-point ordered graph closure, written with increasing endpoints. -/
def RuleP {V : Type*} [LinearOrder V] (G : SimpleGraph V) : Prop :=
  ∀ s t x y, G.Adj s t → G.Adj x y → s ≤ x → x < t → t < y → G.Adj t y

/-- Three-point ordered graph closure. -/
def RuleQ {V : Type*} [LinearOrder V] (G : SimpleGraph V) : Prop :=
  ∀ s t x y z w, G.Adj s t → G.Adj x y → G.Adj z w →
    s ≤ x → x < t → t ≤ y → s ≤ z → z < t → t ≤ w →
    G.Adj (max x z) (max y w)

def Admissible {V : Type*} [LinearOrder V] (G : SimpleGraph V) : Prop :=
  RuleP G ∧ RuleQ G

/-- The full all-admissible-rank, all-defect target, including exact degree and
leading coefficient. This definition does not assert that the target is proved. -/
def FixedDefectPolynomiality : Prop :=
  ∀ i : ℕ, ∃ P : Polynomial ℚ,
    (∀ n : ℕ, i ≤ n+1 → (r n (n+1-i) : ℚ) = P.eval (n : ℚ)) ∧
    P.natDegree = 2*i ∧ P.coeff (2*i) = (i.factorial : ℚ)⁻¹

end CokernelPolynomiality
