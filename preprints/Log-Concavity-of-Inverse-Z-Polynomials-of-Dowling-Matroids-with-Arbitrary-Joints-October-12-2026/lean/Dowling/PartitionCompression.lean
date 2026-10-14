import Dowling.PartitionCompositionSolutions

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

theorem code_none_of_le {p q : GainPartition G n} (hpq : p ≤ q)
    (i : Fin n) (hi : p.code i = none) : q.code i = none := by
  apply (q.solution_zero_iff i).mp
  intro x hx
  exact ((p.mem_solutionSet x).mp (hpq hx)).1 i hi

theorem root_of_le {p q : GainPartition G n} (hpq : p ≤ q)
    (i : Fin n) (hi : q.IsRoot i) : p.IsRoot i := by
  cases hp : p.code i with
  | none =>
    have hq := code_none_of_le hpq i hp
    rw [hi] at hq
    cases hq
  | some v =>
    rcases v with ⟨r,a⟩
    have hrel : ∀ x ∈ q.solutionSet, x i = gainAct G (x r) a :=
      fun x hx => ((p.mem_solutionSet x).mp (hpq hx)).2 i r a hp
    have hqr := q.code_left_of_relation r i i 1 a hi hrel
    have hir := q.least r i (1*a⁻¹) hqr
    have hri := p.least i r a hp
    have he : r = i := le_antisymm hri hir
    subst r
    exact p.rooted i i a hp

def compressedCode (p q : GainPartition G n) (hpq : p ≤ q)
    (i : Fin p.roots.card) : Option (Fin p.roots.card × G) :=
  match hi : q.code (p.rootVertex i) with
  | none => none
  | some (r,g) => some (p.rootOrderIso.symm ⟨r,root_of_le hpq r (q.rooted _ _ _ hi)⟩,g)

theorem compressedCode_none (p q : GainPartition G n) (hpq : p ≤ q)
    (i : Fin p.roots.card) (hi : q.code (p.rootVertex i) = none) :
    compressedCode p q hpq i = none := by
  unfold compressedCode
  split <;> simp_all

theorem compressedCode_some (p q : GainPartition G n) (hpq : p ≤ q)
    (i : Fin p.roots.card) (r : Fin n) (g : G)
    (hi : q.code (p.rootVertex i) = some (r,g)) :
    compressedCode p q hpq i = some (p.rootOrderIso.symm
      ⟨r,root_of_le hpq r (q.rooted _ _ _ hi)⟩,g) := by
  unfold compressedCode
  split
  · rename_i h
    rw [hi] at h
    cases h
  · rename_i r' g' h
    have he := Option.some.inj (hi.symm.trans h)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    rfl

/-- Restriction of an actual coarsening to the free component roots. -/
def compress (p q : GainPartition G n) (hpq : p ≤ q) : GainPartition G p.roots.card where
  code := compressedCode p q hpq
  rooted := by
    intro i j g hij
    cases hi : q.code (p.rootVertex i) with
    | none => rw [compressedCode_none p q hpq i hi] at hij; cases hij
    | some v =>
      rcases v with ⟨r,a⟩
      rw [compressedCode_some p q hpq i r a hi] at hij
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hij)
      have hr : q.code r = some (r,1) := q.rooted _ _ _ hi
      have he : p.rootVertex (p.rootOrderIso.symm ⟨r,root_of_le hpq r hr⟩) = r :=
        congrArg Subtype.val (p.rootOrderIso.apply_symm_apply _)
      apply compressedCode_some p q hpq _ r 1
      rw [he,hr]
  least := by
    intro i j g hij
    cases hi : q.code (p.rootVertex i) with
    | none => rw [compressedCode_none p q hpq i hi] at hij; cases hij
    | some v =>
      rcases v with ⟨r,a⟩
      rw [compressedCode_some p q hpq i r a hi] at hij
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hij)
      have hle : (⟨r,root_of_le hpq r (q.rooted _ _ _ hi)⟩ : {j // p.IsRoot j}) ≤
          p.rootOrderIso i := q.least _ _ _ hi
      simpa only [OrderIso.symm_apply_apply] using p.rootOrderIso.symm.monotone hle

end Dowling.GainPartition
