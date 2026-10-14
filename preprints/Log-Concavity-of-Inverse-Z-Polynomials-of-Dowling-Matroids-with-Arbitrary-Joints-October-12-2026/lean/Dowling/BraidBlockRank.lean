import Dowling.BraidBlockRecover

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

 theorem braidLift_isRoot (p : GainPartition Unit n) (u : Fin (n+1) → G)
    (i : Fin (n+1)) : (p.braidLift u).IsRoot i ↔ p.unitBlockRoot i=i := by
  constructor
  · intro h
    exact congrArg Prod.fst (Option.some.inj h)
  · intro h
    change some (p.unitBlockRoot i,(u (p.unitBlockRoot i))⁻¹*u i)=some (i,1)
    simp [h]

 theorem braidLift_isRoot_zero (p : GainPartition Unit n) (u : Fin (n+1) → G) :
    (p.braidLift u).IsRoot 0 := (braidLift_isRoot p u 0).mpr rfl

 theorem braidLift_isRoot_succ (p : GainPartition Unit n) (u : Fin (n+1) → G)
    (i : Fin n) : (p.braidLift u).IsRoot i.succ ↔ p.IsRoot i := by
  rw [braidLift_isRoot]
  cases hi : p.code i with
  | none => simp [unitBlockRoot,hi,IsRoot,eq_comm]
  | some v =>
    rcases v with ⟨r,g⟩
    cases g
    simp [unitBlockRoot,hi,IsRoot,eq_comm]

 theorem braidLift_roots (p : GainPartition Unit n) (u : Fin (n+1) → G) :
    (p.braidLift u).roots=insert 0 (p.roots.image Fin.succ) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [roots,braidLift_isRoot_zero]
  · simp only [roots,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
      Fin.succ_ne_zero,false_or,Finset.mem_image]
    rw [braidLift_isRoot_succ]
    constructor
    · intro h
      exact ⟨j,h,rfl⟩
    · rintro ⟨k,h,hk⟩
      exact Fin.succ_injective n hk ▸ h

 theorem braidLift_roots_card (p : GainPartition Unit n) (u : Fin (n+1) → G) :
    (p.braidLift u).roots.card=p.roots.card+1 := by
  rw [braidLift_roots,Finset.card_insert_of_notMem,Finset.card_image_of_injective _ (Fin.succ_injective n)]
  simp only [Finset.mem_image]
  rintro ⟨i,_,hi⟩
  exact Fin.succ_ne_zero i hi

 theorem braidLift_rank (p : GainPartition Unit n) (u : Fin (n+1) → G) :
    (n+1)-(p.braidLift u).roots.card=n-p.roots.card := by
  rw [braidLift_roots_card,Nat.add_sub_add_right]

end Dowling.GainPartition
