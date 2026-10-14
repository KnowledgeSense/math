import MainTheorems.PreorderGamma.DemandMatching

namespace ResearchMain.PreorderGamma

variable {L R K : Type*} [Fintype L] [Fintype R] [Fintype K]

omit [Fintype L] [Fintype R] [Fintype K] in
theorem hasTransversal_comp_equiv (e : L ≃ K) (r : K → R → Prop) :
    HasTransversal (fun a : L => r (e a)) ↔ HasTransversal r := by
  constructor
  · rintro ⟨f, hf, hrel⟩
    refine ⟨fun a => f (e.symm a), hf.comp e.symm.injective, ?_⟩
    intro a
    simpa using hrel (e.symm a)
  · rintro ⟨f, hf, hrel⟩
    exact ⟨fun a => f (e a), hf.comp e.injective, fun a => hrel (e a)⟩

omit [Fintype R] [Fintype K] in
noncomputable def demandCellsSupportEquiv (d : L → ℕ) (hones : ∀ a, d a ≤ 1) :
    DemandCells d ≃ (demandSupport d) := by
  classical
  refine
    { toFun := fun c => ⟨c.1, ?_⟩
      invFun := fun a => ⟨a.val, ⟨0, ?_⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · simp only [demandSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.zero_lt_of_lt c.2.isLt
  · simpa [demandSupport] using a.property
  · rintro ⟨a, k⟩
    change (⟨a, ⟨0, _⟩⟩ : DemandCells d) = ⟨a, k⟩
    apply congrArg (fun q : Fin (d a) => (⟨a, q⟩ : DemandCells d))
    apply Fin.ext
    have hk := k.isLt
    have hone := hones a
    omega
  · intro a
    rfl

omit [Fintype K] in
theorem binary_demand_iff_support_transversal (r : L → R → Prop) (d : L → ℕ)
    (hones : ∀ a, d a ≤ 1) :
    IsDemand r d ↔ HasTransversal (fun a : demandSupport d => r a.val) := by
  rw [demand_iff_cell_transversal]
  exact hasTransversal_comp_equiv (demandCellsSupportEquiv d hones)
    (fun a : demandSupport d => r a.val)

omit [Fintype K] in
theorem hasTransversal_iff_equiv (r : L → R → Prop) (hc : Fintype.card L = Fintype.card R) :
    HasTransversal r ↔ ∃ f : L ≃ R, ∀ a, r a (f a) := by
  classical
  constructor
  · rintro ⟨f, hf, hrel⟩
    exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩), hrel⟩
  · rintro ⟨f, hrel⟩
    exact ⟨f, f.injective, hrel⟩

omit [Fintype K] in
theorem maximal_support_hasPerfectMatching {r : L → R → Prop} {d : L → ℕ}
    (hd : IsDemand r d) (hc : (demandSupport d).card = Fintype.card R) :
    ∃ f : (demandSupport d) ≃ R, ∀ a, r a.val (f a) := by
  classical
  have hones : ∀ a, d a ≤ 1 := by
    intro a
    rw [maximal_support_is_indicator hd hc a]
    split_ifs <;> omega
  apply (hasTransversal_iff_equiv _ (by simpa using hc)).mp
  exact (binary_demand_iff_support_transversal r d hones).mp hd

end ResearchMain.PreorderGamma
