import PenneyDensity.PrescribedCoordinates

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

structure DirectedMatching (α β : Type*) where
  pivot : β → α
  parent : β → α
  pivot_injective : Function.Injective pivot
  parent_not_pivot : ∀ b c,parent b≠pivot c

namespace DirectedMatching
variable {α β γ : Type*}

 abbrev Free (M : DirectedMatching α β) := {i : α // ¬∃ b,M.pivot b=i}

 def freeParent (M : DirectedMatching α β) (b : β) : M.Free :=
  ⟨M.parent b,by rintro ⟨c,hc⟩; exact M.parent_not_pivot b c hc.symm⟩

 def extend (M : DirectedMatching α β) (g : M.Free → Bool) (i : α) : Bool :=
  if hi : ∃ b,M.pivot b=i then g (M.freeParent (Classical.choose hi)) else g ⟨i,hi⟩

 theorem extend_free (M : DirectedMatching α β) (g : M.Free → Bool) (i : M.Free) :
    M.extend g i.val=g i := by
  simp only [extend,dite_eq_right i.property]

 theorem extend_pivot (M : DirectedMatching α β) (g : M.Free → Bool) (b : β) :
    M.extend g (M.pivot b)=g (M.freeParent b) := by
  have hb : ∃ c,M.pivot c=M.pivot b := ⟨b,rfl⟩
  rw [extend,dite_eq_left hb]
  exact congrArg (fun c => g (M.freeParent c)) (M.pivot_injective (Classical.choose_spec hb))

 def constrainedEquiv (M : DirectedMatching α β) (fixed : γ → M.Free) (values : γ → Bool) :
    {f : α → Bool // (∀ b,f (M.pivot b)=f (M.parent b)) ∧
      ∀ c,f (fixed c).val=values c} ≃
    {g : M.Free → Bool // ∀ c,g (fixed c)=values c} where
  toFun f := ⟨fun i => f.val i.val,f.property.2⟩
  invFun g := ⟨M.extend g.val,by
    constructor
    · intro b
      rw [M.extend_pivot]
      exact (M.extend_free g.val (M.freeParent b)).symm
    · intro c
      rw [M.extend_free]
      exact g.property c⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    change M.extend (fun j : M.Free => f.val j.val) i=f.val i
    by_cases hi : ∃ b,M.pivot b=i
    · obtain ⟨b,rfl⟩ := hi
      rw [M.extend_pivot]
      exact (f.property.1 b).symm
    · exact M.extend_free (fun j => f.val j.val) ⟨i,hi⟩
  right_inv g := by
    apply Subtype.ext
    funext i
    exact M.extend_free g.val i

 theorem card_fixed_matching [Fintype α] [Fintype β] [Fintype γ]
    (M : DirectedMatching α β) (fixed : γ → M.Free) (hf : Function.Injective fixed)
    (values : γ → Bool) :
    Fintype.card {f : α → Bool // (∀ b,f (M.pivot b)=f (M.parent b)) ∧
      ∀ c,f (fixed c).val=values c}=2^(Fintype.card α-Fintype.card β-Fintype.card γ) := by
  rw [Fintype.card_congr (M.constrainedEquiv fixed values)]
  have hc : Fintype.card {g : M.Free → Bool // ∀ c,g (fixed c)=values c}=
      2^(Fintype.card M.Free-Fintype.card γ) := by
    convert card_prescribed_coordinates fixed hf values using 1
    exact congrArg (@Fintype.card {g : M.Free → Bool // ∀ c,g (fixed c)=values c}) (Subsingleton.elim _ _)
  rw [hc]
  have hfree : Fintype.card M.Free=Fintype.card α-Fintype.card β := by
    rw [Fintype.card_subtype_compl]
    have hr : Fintype.card {i : α // ∃ b,M.pivot b=i}=Fintype.card β := by
      convert (Fintype.card_congr (Equiv.ofInjective M.pivot M.pivot_injective)).symm using 1
      exact congrArg (@Fintype.card {i : α // ∃ b,M.pivot b=i}) (Subsingleton.elim _ _)
    rw [hr]
  rw [hfree]

end DirectedMatching
end PenneyDensity
