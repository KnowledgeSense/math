import R34.Transfer
import Mathlib.Data.List.Sigma

namespace R34.ExpandedWords

variable {α : Type*}

/-- A neutral or contracted site, or a site carrying charges. -/
abbrev Atom (α : Type*) := Bool ⊕ α

structure Blocks (α : Type*) where
  leading : List Bool
  charged : List (α × List Bool)

def flatten (b : Blocks α) : List (Atom α) :=
  b.leading.map Sum.inl ++ b.charged.flatMap
    (fun p => Sum.inr p.1 :: p.2.map Sum.inl)

def blocks : List (Atom α) → Blocks α
  | [] => ⟨[], []⟩
  | Sum.inl flag :: rest =>
    let b := blocks rest
    ⟨flag :: b.leading, b.charged⟩
  | Sum.inr site :: rest =>
    let b := blocks rest
    ⟨[], (site, b.leading) :: b.charged⟩

@[simp] theorem flatten_blocks (word : List (Atom α)) : flatten (blocks word) = word := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
    cases a with
    | inl flag =>
      simp only [blocks, flatten, List.map_cons, List.cons_append]
      congr 1
    | inr site =>
      simp only [blocks, flatten, List.map_nil, List.nil_append, List.flatMap_cons,
        List.cons_append]
      congr 1

noncomputable def neutralMatrix (flag : Bool) : Transfer.Mat :=
  if flag then Transfer.contractedPair else 1

noncomputable def atomMatrix (charged : α → Transfer.Mat) : Atom α → Transfer.Mat
  | Sum.inl flag => neutralMatrix flag
  | Sum.inr site => charged site

noncomputable def matrixBlocks (charged : α → Transfer.Mat) (b : Blocks α) : List Transfer.Mat :=
  b.leading.map neutralMatrix ++ b.charged.flatMap
    (fun p => charged p.1 :: p.2.map neutralMatrix)

theorem map_flatten (charged : α → Transfer.Mat) (b : Blocks α) :
    (flatten b).map (atomMatrix charged) = matrixBlocks charged b := by
  simp [flatten, matrixBlocks, List.map_append, List.map_flatMap, List.map_map,
    atomMatrix, Function.comp_def]

theorem value_blocks (charged : α → Transfer.Mat) (word : List (Atom α)) :
    Transfer.value (word.map (atomMatrix charged)) =
      Transfer.value (matrixBlocks charged (blocks word)) := by
  rw [← map_flatten, flatten_blocks]

end R34.ExpandedWords
