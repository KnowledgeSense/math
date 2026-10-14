import CokernelPolynomiality.OrderRestriction
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.DeriveFintype

namespace CokernelPolynomiality

inductive Vertex (i m : ℕ) where
  | root : Vertex i m
  | exceptional : Fin i → Vertex i m
  | regular : Fin m → Vertex i m
  deriving DecidableEq, Fintype

/-- A regular vertex is at the start of its gap; exceptional vertices are
ordered within their prescribed gap by their labels. -/
def position {i m : ℕ} (d : Fin i → Fin (m+1)) : Vertex i m → ℕ ×ₗ ℕ
  | .root => toLex (0,0)
  | .exceptional j => toLex ((d j).val,j.val+1)
  | .regular t => toLex (t.val+1,0)

 theorem position_injective {i m : ℕ} (d : Fin i → Fin (m+1)) :
    Function.Injective (position d) := by
  intro u v h
  have h1 := congrArg (fun z : ℕ ×ₗ ℕ => (ofLex z).1) h
  have h2 := congrArg (fun z : ℕ ×ₗ ℕ => (ofLex z).2) h
  cases u <;> cases v <;> simp only [position, ofLex_toLex] at h1 h2
  all_goals first | rfl | omega | (congr 1; apply Fin.ext; omega)

abbrev codeOrder {i m : ℕ} (d : Fin i → Fin (m+1)) : LinearOrder (Vertex i m) :=
  LinearOrder.lift' (position d) (position_injective d)

/-- The graph specified by regular-neighborhood cutoffs and exceptional edges. -/
def codeAdj {i m : ℕ} (y : Fin i → Fin (m+1)) (E : SimpleGraph (Fin i)) :
    Vertex i m → Vertex i m → Prop
  | .root, .regular _ => True
  | .regular _, .root => True
  | .regular j, .regular k => j ≠ k
  | .exceptional j, .regular t => (y j).val < t.val+1
  | .regular t, .exceptional j => (y j).val < t.val+1
  | .exceptional j, .exceptional k => E.Adj j k
  | _, _ => False

def codeGraph {i m : ℕ} (y : Fin i → Fin (m+1)) (E : SimpleGraph (Fin i)) :
    SimpleGraph (Vertex i m) where
  Adj := codeAdj y E
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> simp_all [codeAdj, ne_comm, SimpleGraph.adj_comm]⟩
  loopless := ⟨by intro u; cases u <;> simp [codeAdj]⟩

structure Code (i m : ℕ) where
  d : Fin i → Fin (m+1)
  y : Fin i → Fin (m+1)
  epsilon : SimpleGraph (Fin i)
  monotone_d : Monotone d

 theorem Code.data_injective (i m : ℕ) : Function.Injective
    (fun c : Code i m => (c.d,c.y,c.epsilon)) := by
  intro a b hab
  cases a
  cases b
  simp only [Prod.mk.injEq] at hab
  rcases hab with ⟨hd,hy,he⟩
  cases hd
  cases hy
  cases he
  rfl

instance (i m : ℕ) : Finite (Code i m) := Finite.of_injective _ (Code.data_injective i m)
noncomputable instance (i m : ℕ) : Fintype (Code i m) := Fintype.ofFinite _

/-- The exact finite-template admissibility predicate, with no conclusion
about admissibility built into the data. -/
def Code.IsAdmissible {i m : ℕ} (c : Code i m) : Prop :=
  @Admissible (Vertex i m) (codeOrder c.d) (codeGraph c.y c.epsilon)

def Code.IsNormalized {i q : ℕ} (c : Code i q) : Prop :=
  ∀ k : Fin (q+1), k ≠ 0 → ∃ j, c.d j = k ∨ c.y j = k

/-- The source's structurally defined nonnegative binomial coefficients. -/
noncomputable def templateCount (i q : ℕ) : ℕ := by
  classical
  exact Fintype.card { c : Code i q // c.IsAdmissible ∧ c.IsNormalized }

end CokernelPolynomiality
