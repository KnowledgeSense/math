import Dowling.GainEquations
import Mathlib.Data.Fintype.Basic

noncomputable section
namespace Dowling
open scoped Classical

/-- Canonical potential blocks: each nonzero block is rooted at its least vertex,
with potential one at that root. Vertices assigned none form the zero block. -/
structure GainPartition (G : Type*) [Group G] (n : ℕ) where
  code : Fin n → Option (Fin n × G)
  rooted : ∀ i j g, code i = some (j,g) → code j = some (j,1)
  least : ∀ i j g, code i = some (j,g) → j ≤ i

variable {G : Type*} [Group G] {n : ℕ}

namespace GainPartition

def IsRoot (p : GainPartition G n) (j : Fin n) : Prop := p.code j = some (j,1)

def roots (p : GainPartition G n) : Finset (Fin n) := Finset.univ.filter p.IsRoot

/-- Every free block receives an independent group-or-zero value. -/
def assignment (p : GainPartition G n) (a : Fin n → Option G) (i : Fin n) : Option G :=
  match p.code i with
  | none => none
  | some (j,g) => gainAct G (a j) g

def solutionSet (p : GainPartition G n) : Set (Fin n → Option G) :=
  Set.range p.assignment

@[simp] theorem assignment_root (p : GainPartition G n) (a : Fin n → Option G)
    (j : Fin n) (hj : p.IsRoot j) : p.assignment a j = a j := by
  change p.code j = some (j,1) at hj
  simp only [assignment, hj, gainAct_one]

theorem assignment_none (p : GainPartition G n) (a : Fin n → Option G)
    (i : Fin n) (hi : p.code i = none) : p.assignment a i = none := by
  simp only [assignment, hi]

theorem assignment_some (p : GainPartition G n) (a : Fin n → Option G)
    (i j : Fin n) (g : G) (hi : p.code i = some (j,g)) :
    p.assignment a i = gainAct G (p.assignment a j) g := by
  rw [assignment_root p a j (p.rooted i j g hi)]
  simp only [assignment, hi]

/-- The parameterization is exactly the block equations, not only a subset of solutions. -/
theorem mem_solutionSet (p : GainPartition G n) (x : Fin n → Option G) :
    x ∈ p.solutionSet ↔
      (∀ i, p.code i = none → x i = none) ∧
      (∀ i j g, p.code i = some (j,g) → x i = gainAct G (x j) g) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨fun i hi => p.assignment_none a i hi,
      fun i j g hi => p.assignment_some a i j g hi⟩
  · rintro ⟨hz, he⟩
    refine ⟨x, ?_⟩
    funext i
    cases hi : p.code i with
    | none => simp only [assignment, hi, hz i hi]
    | some v =>
      rcases v with ⟨j,g⟩
      simpa only [assignment, hi] using (he i j g hi).symm

/-- The empty edge set leaves every vertex as its own balanced free component. -/
def discrete : GainPartition G n where
  code i := some (i,1)
  rooted := by
    intro i j g h
    have h' : (i,(1:G)) = (j,g) := Option.some.inj h
    have hij : i = j := congrArg Prod.fst h'
    subst j
    rfl
  least := by
    intro i j g h
    have h' : (i,(1:G)) = (j,g) := Option.some.inj h
    have hij : i = j := congrArg Prod.fst h'
    subst j
    exact le_rfl

@[simp] theorem discrete_assignment (a : Fin n → Option G) : discrete.assignment a = a := by
  funext i
  simp [assignment, discrete]

theorem discrete_solutionSet : (discrete : GainPartition G n).solutionSet = Set.univ := by
  ext a
  constructor
  · intro _; trivial
  · intro _
    exact ⟨a, discrete_assignment a⟩

end GainPartition
end Dowling
