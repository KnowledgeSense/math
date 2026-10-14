import Dowling.RootCoordinates

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- The last vertex is either a new free singleton, zero, or attached to one
existing free component with a uniquely determined group potential. -/
abbrev LastChoice (p : GainPartition G n) := Option (Option ({j // p.IsRoot j} × G))

def lastCode (p : GainPartition G n) (c : p.LastChoice) : Option (Fin (n+1) × G) :=
  match c with
  | none => some (Fin.last n,1)
  | some none => none
  | some (some (r,g)) => some (r.val.castSucc,g)

def appendCode (p : GainPartition G n) (c : p.LastChoice) : Fin (n+1) → Option (Fin (n+1) × G) :=
  Fin.lastCases (p.lastCode c) (fun i => (p.code i).map (fun v => (v.1.castSucc,v.2)))

@[simp] theorem appendCode_old (p : GainPartition G n) (c : p.LastChoice) (i : Fin n) :
    p.appendCode c i.castSucc = (p.code i).map (fun v => (v.1.castSucc,v.2)) := by
  simp [appendCode]

@[simp] theorem appendCode_last (p : GainPartition G n) (c : p.LastChoice) :
    p.appendCode c (Fin.last n) = p.lastCode c := by
  simp [appendCode]

def append (p : GainPartition G n) (c : p.LastChoice) : GainPartition G (n+1) where
  code := p.appendCode c
  rooted := by
    intro i j g hij
    induction i using Fin.lastCases with
    | last =>
      rw [appendCode_last] at hij
      cases c with
      | none =>
        change some (Fin.last n,(1:G)) = some (j,g) at hij
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hij)
        exact p.appendCode_last none
      | some c =>
        cases c with
        | none => cases hij
        | some v =>
          rcases v with ⟨r,a⟩
          change some (r.val.castSucc,a) = some (j,g) at hij
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hij)
          rw [appendCode_old,r.property]
          rfl
    | cast i =>
      rw [appendCode_old] at hij
      cases hi : p.code i with
      | none => simp [hi] at hij
      | some v =>
        rcases v with ⟨r,a⟩
        simp only [hi,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hij
        obtain ⟨rfl,rfl⟩ := hij
        rw [appendCode_old,p.rooted i r a hi]
        rfl
  least := by
    intro i j g hij
    induction i using Fin.lastCases with
    | last => exact Fin.le_last _
    | cast i =>
      rw [appendCode_old] at hij
      cases hi : p.code i with
      | none => simp [hi] at hij
      | some v =>
        rcases v with ⟨r,a⟩
        simp only [hi,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hij
        obtain ⟨rfl,rfl⟩ := hij
        exact p.least i r a hi

end Dowling.GainPartition
