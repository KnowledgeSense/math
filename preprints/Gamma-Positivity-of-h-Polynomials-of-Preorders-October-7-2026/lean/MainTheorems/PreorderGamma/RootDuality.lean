import MainTheorems.PreorderGamma.RootLattice

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

omit [Fintype E] [DecidableEq E] in
theorem augmentedRelation_orderDual_swap (i j : Option E) :
    augmentedRelation (E := OrderDual E) j i ↔ augmentedRelation (E := E) i j := by
  cases i <;> cases j <;> rfl

def NaturalTransport.orderDualSwap {u v : Option E → ℕ}
    (p : NaturalTransport (augmentedRelation (E := E)) u v) :
    NaturalTransport (augmentedRelation (E := OrderDual E)) v u where
  flow j i := p.flow i j
  supported j i h := p.supported i j
    (fun hrel => h ((augmentedRelation_orderDual_swap (E := E) i j).mpr hrel))
  row_sum j := p.column_sum j
  column_sum i := p.row_sum i

noncomputable def rootNaturalOrderDualEquiv (t : ℕ) :
    RootNaturalMargins (E := E) t ≃ RootNaturalMargins (E := OrderDual E) t where
  toFun z := ⟨z.val.swap, z.property.2.1, z.property.1, by
    obtain ⟨p⟩ := z.property.2.2
    exact ⟨p.orderDualSwap⟩⟩
  invFun z := ⟨z.val.swap, z.property.2.1, z.property.1, by
    obtain ⟨p⟩ := z.property.2.2
    exact ⟨p.orderDualSwap⟩⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

noncomputable def rootIntegerOrderDualEquiv (t : ℕ) :
    {z : (Option E → ℤ) × (Option E → ℤ) // RootIntegerPoints (E := E) t z} ≃
      {z : (Option E → ℤ) × (Option E → ℤ) //
        RootIntegerPoints (E := OrderDual E) t z} :=
  (rootIntegerNaturalEquiv (E := E) t).trans
    ((rootNaturalOrderDualEquiv t).trans (rootIntegerNaturalEquiv (E := OrderDual E) t).symm)

theorem rootIntegerOrderDualEquiv_val (t : ℕ)
    (z : {z : (Option E → ℤ) × (Option E → ℤ) // RootIntegerPoints (E := E) t z}) :
    (rootIntegerOrderDualEquiv t z).val = z.val.swap := by
  apply Prod.ext <;> funext i
  · exact Int.toNat_of_nonneg ((rootIntegerPoints_nonnegative z.property).2 i)
  · exact Int.toNat_of_nonneg ((rootIntegerPoints_nonnegative z.property).1 i)

theorem root_lattice_count_orderDual (t : ℕ) :
    rootLatticeCount (E := E) t = rootLatticeCount (E := OrderDual E) t :=
  Nat.card_congr (rootIntegerOrderDualEquiv t)

end ResearchMain.PreorderGamma
