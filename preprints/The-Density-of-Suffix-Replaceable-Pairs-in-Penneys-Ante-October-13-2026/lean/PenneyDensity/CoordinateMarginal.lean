import PenneyDensity.FiniteProbability

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

 def coordinateSplit {α β : Type*} (e : β → α) (he : Function.Injective e) :
    (α → Bool) ≃ (β → Bool) × ({i : α // ¬∃ b,e b=i} → Bool) where
  toFun f := (fun b => f (e b),fun i => f i.val)
  invFun p i := if hi : ∃ b,e b=i then p.1 (Classical.choose hi) else p.2 ⟨i,hi⟩
  left_inv f := by
    funext i
    by_cases hi : ∃ b,e b=i
    · simp only [dite_eq_left hi]
      exact congrArg f (Classical.choose_spec hi)
    · simp only [dite_eq_right hi]
  right_inv p := by
    apply Prod.ext
    · funext b
      have hb : ∃ c,e c=e b := ⟨b,rfl⟩
      simp only [dite_eq_left hb]
      exact congrArg p.1 (he (Classical.choose_spec hb))
    · funext i
      simp only [dite_eq_right i.property]

 theorem probability_first {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (P : α → Prop) : probability (fun p : α × β => P p.1)=probability P := by
  let e : {p : α × β // P p.1} ≃ {a : α // P a} × β :=
    { toFun := fun p => (⟨p.val.1,p.property⟩,p.val.2)
      invFun := fun p => ⟨(p.1.val,p.2),p.1.property⟩
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  simp only [probability,Nat.card_eq_fintype_card]
  rw [Fintype.card_congr e,Fintype.card_prod,Fintype.card_prod]
  push_cast
  have hb : (Fintype.card β : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_div_mul_right _ _ hb

/-- Independent fair bits restricted to any injective family of coordinates
are again uniform, with the exact original counting normalization. -/
theorem probability_coordinate_pullback {α β : Type*} [Fintype α] [Fintype β]
    (e : β → α) (he : Function.Injective e) (P : (β → Bool) → Prop) :
    probability (fun f : α → Bool => P (fun b => f (e b)))=probability P := by
  exact (probability_equal_of_equiv (coordinateSplit e he)
    (fun f => P (fun b => f (e b))) (fun p => P p.1) (fun _ => Iff.rfl)).trans
      (probability_first P)

end PenneyDensity
