import PenneyDensity.CoordinateMarginal

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

 def prescribedCoordinatesEquiv {α β : Type*} (e : β → α) (he : Function.Injective e)
    (v : β → Bool) : {f : α → Bool // ∀ b,f (e b)=v b} ≃
      ({i : α // ¬∃ b,e b=i} → Bool) where
  toFun f := (coordinateSplit e he f.val).2
  invFun g := ⟨(coordinateSplit e he).symm (v,g),by
    have hh := congrArg Prod.fst ((coordinateSplit e he).apply_symm_apply (v,g))
    exact congrFun hh⟩
  left_inv f := by
    apply Subtype.ext
    apply (coordinateSplit e he).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · funext b
      exact (f.property b).symm
    · rfl
  right_inv g := by
    exact congrArg Prod.snd ((coordinateSplit e he).apply_symm_apply (v,g))

 theorem card_prescribed_coordinates {α β : Type*} [Fintype α] [Fintype β]
    (e : β → α) (he : Function.Injective e) (v : β → Bool) :
    Fintype.card {f : α → Bool // ∀ b,f (e b)=v b}=2^(Fintype.card α-Fintype.card β) := by
  rw [Fintype.card_congr (prescribedCoordinatesEquiv e he v),Fintype.card_fun,Fintype.card_bool,
    Fintype.card_subtype_compl]
  have hr : Fintype.card {i : α // ∃ b,e b=i}=Fintype.card β := by
    convert (Fintype.card_congr (Equiv.ofInjective e he)).symm using 1
    exact congrArg (@Fintype.card {i : α // ∃ b,e b=i}) (Subsingleton.elim _ _)
  rw [hr]

end PenneyDensity
