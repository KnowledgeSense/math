import MainTheorems.PreorderReciprocity.Compositions

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {T : Type*} [Fintype T]

abbrev PositiveCoefficients (T : Type*) [Fintype T] (t : ℕ) :=
  {c : T → ℕ // (∀ i, 0 < c i) ∧ (∑ i, c i) ≤ t}

theorem positiveCoefficients_dimension_bound {t : ℕ} (c : PositiveCoefficients T t) :
    Fintype.card T ≤ t := by
  have h : (∑ _i : T, (1 : ℕ)) ≤ ∑ i, c.val i :=
    Finset.sum_le_sum (fun i hi => c.property.1 i)
  have hs : (∑ _i : T, (1 : ℕ)) = Fintype.card T := by simp
  rw [hs] at h
  exact h.trans c.property.2

def positiveCoefficientsEquiv {t : ℕ} (ht : Fintype.card T ≤ t) :
    PositiveCoefficients T t ≃ {c : T → ℕ // (∑ i, c i) ≤ t - Fintype.card T} where
  toFun c := ⟨fun i => c.val i - 1, by
    have hsum : (∑ i, (c.val i - 1)) + Fintype.card T = ∑ i, c.val i := by
      calc
        _ = ∑ i, ((c.val i - 1) + 1) := by simp [Finset.sum_add_distrib]
        _ = ∑ i, c.val i := Finset.sum_congr rfl (fun i hi => by have h := c.property.1 i; omega)
    have h := c.property.2
    change (∑ i, (c.val i - 1)) ≤ t - Fintype.card T
    omega⟩
  invFun c := ⟨fun i => c.val i + 1, fun i => Nat.succ_pos _, by
    have hsum : (∑ i, (c.val i + 1)) = (∑ i, c.val i) + Fintype.card T := by
      simp [Finset.sum_add_distrib]
    rw [hsum]
    have h := c.property
    omega⟩
  left_inv := by
    intro c
    apply Subtype.ext
    funext i
    have h := c.property.1 i
    change c.val i - 1 + 1 = c.val i
    omega
  right_inv := by
    intro c
    apply Subtype.ext
    funext i
    exact Nat.add_sub_cancel _ _

instance positiveCoefficientsFinite (t : ℕ) : Finite (PositiveCoefficients T t) := by
  let f : PositiveCoefficients T t → T → Fin (t + 1) := fun c i =>
    ⟨c.val i, Nat.lt_succ_of_le (by
      have hi : c.val i ≤ ∑ j, c.val j :=
        Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
      exact hi.trans c.property.2)⟩
  apply Finite.of_injective f
  intro c d h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

noncomputable def boundedCoefficientReindex (k : ℕ) :
    {c : T → ℕ // (∑ i, c i) ≤ k} ≃
      {c : Fin (Fintype.card T) → ℕ // (∑ i, c i) ≤ k} := by
  let e := Fintype.equivFin T
  refine
    { toFun := fun c => ⟨fun i => c.val (e.symm i), ?_⟩
      invFun := fun c => ⟨fun i => c.val (e i), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h : (∑ i : Fin (Fintype.card T), c.val (e.symm i)) = ∑ i : T, c.val i := by
      apply Fintype.sum_equiv e.symm
      intro i
      rfl
    rw [h]
    exact c.property
  · have h : (∑ i : T, c.val (e i)) = ∑ i : Fin (Fintype.card T), c.val i := by
      apply Fintype.sum_equiv e
      intro i
      rfl
    rw [h]
    exact c.property
  · intro c
    apply Subtype.ext
    funext i
    simp
  · intro c
    apply Subtype.ext
    funext i
    simp

theorem positiveCoefficients_count (t : ℕ) :
    Nat.card (PositiveCoefficients T t) = Nat.choose t (Fintype.card T) := by
  by_cases ht : Fintype.card T ≤ t
  · rw [Nat.card_congr (positiveCoefficientsEquiv (T := T) ht),
      Nat.card_congr (boundedCoefficientReindex (T := T) (t - Fintype.card T)),
      PreorderReciprocity.bounded_composition_count]
    have hshift : Fintype.card T + (t - Fintype.card T) = t := by omega
    rw [hshift]
    exact Nat.choose_symm ht
  · let : IsEmpty (PositiveCoefficients T t) :=
      ⟨fun c => ht (positiveCoefficients_dimension_bound c)⟩
    rw [Nat.card_of_isEmpty, Nat.choose_eq_zero_of_lt (lt_of_not_ge ht)]

end ResearchMain.PreorderGamma.SimplicialRealization
