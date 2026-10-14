import Dowling.PartitionAppend

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

def dropCode (p : GainPartition G (n+1)) (i : Fin n) : Option (Fin n × G) :=
  match hi : p.code i.castSucc with
  | none => none
  | some (r,g) => some (⟨r.val,lt_of_le_of_lt (p.least _ _ _ hi) i.isLt⟩,g)

theorem dropCode_none (p : GainPartition G (n+1)) (i : Fin n)
    (hi : p.code i.castSucc = none) : p.dropCode i = none := by
  unfold dropCode
  split <;> simp_all

theorem dropCode_some (p : GainPartition G (n+1)) (i : Fin n) (r : Fin (n+1)) (g : G)
    (hi : p.code i.castSucc = some (r,g)) :
    p.dropCode i = some (⟨r.val,lt_of_le_of_lt (p.least _ _ _ hi) i.isLt⟩,g) := by
  unfold dropCode
  split
  · rename_i h
    rw [hi] at h
    cases h
  · rename_i r' g' h
    have he := Option.some.inj (hi.symm.trans h)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    rfl

def drop (p : GainPartition G (n+1)) : GainPartition G n where
  code := p.dropCode
  rooted := by
    intro i j g hij
    cases hi : p.code i.castSucc with
    | none => rw [p.dropCode_none i hi] at hij; cases hij
    | some v =>
      rcases v with ⟨r,a⟩
      rw [p.dropCode_some i r a hi] at hij
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hij)
      have hr := p.rooted _ _ _ hi
      have hc : (⟨r.val,lt_of_le_of_lt (p.least _ _ _ hi) i.isLt⟩ : Fin n).castSucc = r :=
        Fin.ext rfl
      have hr' : p.code (⟨r.val,lt_of_le_of_lt (p.least _ _ _ hi) i.isLt⟩ : Fin n).castSucc = some (r,1) := by
        rw [hc]; exact hr
      rw [p.dropCode_some _ r 1 hr']
  least := by
    intro i j g hij
    cases hi : p.code i.castSucc with
    | none => rw [p.dropCode_none i hi] at hij; cases hij
    | some v =>
      rcases v with ⟨r,a⟩
      rw [p.dropCode_some i r a hi] at hij
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hij)
      exact p.least _ _ _ hi

/-- Restriction retains every old code exactly under the inclusion of vertices. -/
theorem drop_code_map (p : GainPartition G (n+1)) (i : Fin n) :
    (p.drop.code i).map (fun v => (v.1.castSucc,v.2)) = p.code i.castSucc := by
  cases hi : p.code i.castSucc with
  | none => rw [show p.drop.code i = none from p.dropCode_none i hi]; rfl
  | some v =>
    rcases v with ⟨r,a⟩
    rw [show p.drop.code i = _ from p.dropCode_some i r a hi]
    congr 2

end Dowling.GainPartition
