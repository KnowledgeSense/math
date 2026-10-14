import MainTheorems.Tuza.FanCardinality

namespace ResearchMain.Tuza

def removedLeftEquiv {F V : Type*} (c : F) :
    {x : F ⊕ V // x ≠ .inl c} ≃ ({x : F // x ≠ c} ⊕ V) where
  toFun x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl d => exact .inl ⟨d, fun h => hx (congrArg Sum.inl h)⟩
    | inr v => exact .inr v
  invFun x := by
    cases x with
    | inl d => exact ⟨.inl d.val, fun h => d.property (Sum.inl_injective h)⟩
    | inr v => exact ⟨.inr v, by intro h; cases h⟩
  left_inv := by intro x; obtain ⟨x, hx⟩ := x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

def removedLeftIso {F V : Type*} (c : F) :
    (fanGraph F V).induce {x | x ≠ .inl c} ≃g fanGraph {x : F // x ≠ c} V where
  toEquiv := removedLeftEquiv c
  map_rel_iff' := by
    intro x y
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    cases x <;> cases y <;> rfl

def fanCenterIso {F F' V : Type*} (e : F ≃ F') : fanGraph F V ≃g fanGraph F' V where
  toEquiv := Equiv.sumCongr e (Equiv.refl V)
  map_rel_iff' := by intro x y; cases x <;> cases y <;> rfl

theorem removed_five_centers {V : Type*} :
    Nonempty ((fanGraph (Fin 5) V).induce {x | x ≠ .inl (Fin.last 4)} ≃g fanGraph (Fin 4) V) := by
  classical
  let e : {x : Fin 5 // x ≠ Fin.last 4} ≃ Fin 4 := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl]
    simp)
  exact ⟨(removedLeftIso (V := V) (Fin.last 4)).trans (fanCenterIso e)⟩

end ResearchMain.Tuza
