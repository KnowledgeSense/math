import MainTheorems.Hypercomb.Hypergraphs

namespace ResearchMain.Hypercomb

open Classical

abbrev SmallSet (V : Type*) := {S : Finset V // S.card ≤ 1}

abbrev Excluded {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (r : V) :=
  {S : Finset V // StrongIndependent H S ∧ r ∉ S}

abbrev Included {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (r : V) :=
  {S : Finset V // StrongIndependent H S ∧ r ∈ S}

noncomputable instance {V : Type*} [Fintype V] : Fintype (SmallSet V) := Fintype.ofFinite _

noncomputable instance {V : Type*} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (r : V) :
    Fintype (Excluded H r) := Fintype.ofFinite _

noncomputable instance {V : Type*} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (r : V) :
    Fintype (Included H r) := Fintype.ofFinite _

def optionSmallSet {V : Type*} (o : Option V) : SmallSet V :=
  ⟨o.toFinset, by cases o <;> simp⟩

theorem optionSmallSet_injective {V : Type*} : Function.Injective (@optionSmallSet V) := by
  intro o p he
  have hval := congrArg Subtype.val he
  cases o <;> cases p <;> simp [optionSmallSet] at hval ⊢
  exact hval

theorem optionSmallSet_surjective {V : Type*} [DecidableEq V] : Function.Surjective (@optionSmallSet V) := by
  intro S
  obtain he | ⟨x, hx⟩ := S.val.eq_empty_or_nonempty
  · refine ⟨none, Subtype.ext ?_⟩
    exact he.symm
  · have he : S.val = {x} := by
      ext y
      constructor
      · intro hy
        exact Finset.mem_singleton.mpr (Finset.card_le_one.mp S.property y hy x hx)
      · intro hy
        rw [Finset.mem_singleton.mp hy]
        exact hx
    exact ⟨some x, Subtype.ext he.symm⟩

noncomputable def optionSmallSetEquiv {V : Type*} [DecidableEq V] : Option V ≃ SmallSet V :=
  Equiv.ofBijective optionSmallSet ⟨optionSmallSet_injective, optionSmallSet_surjective⟩

noncomputable def excludedPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (r : V) : Polynomial ℝ := ∑ S : Excluded H r, Polynomial.X ^ S.val.card

noncomputable def includedPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (r : V) : Polynomial ℝ := ∑ S : Included H r, Polynomial.X ^ S.val.card

theorem smallSet_polynomial {V : Type*} [Fintype V] [DecidableEq V] :
    (∑ S : SmallSet V, (Polynomial.X : Polynomial ℝ) ^ S.val.card) =
      1 + Polynomial.C (Fintype.card V : ℝ) * Polynomial.X := by
  rw [← Equiv.sum_comp (optionSmallSetEquiv (V := V))]
  change (∑ o : Option V, (Polynomial.X : Polynomial ℝ) ^ o.toFinset.card) = _
  rw [Fintype.sum_option]
  simp only [Option.toFinset_none, Option.toFinset_some, Finset.card_empty, Finset.card_singleton,
    pow_zero, pow_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  norm_cast

theorem independentPolynomial_partition {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (r : V) :
    (∑ S ∈ Finset.univ.filter (StrongIndependent H), (Polynomial.X : Polynomial ℝ) ^ S.card) =
      excludedPolynomial H r + includedPolynomial H r := by
  rw [excludedPolynomial, includedPolynomial,
    ← Finset.sum_subtype (Finset.univ.filter (fun S => StrongIndependent H S ∧ r ∉ S))
      (fun S => by simp) (fun S => (Polynomial.X : Polynomial ℝ) ^ S.card),
    ← Finset.sum_subtype (Finset.univ.filter (fun S => StrongIndependent H S ∧ r ∈ S))
      (fun S => by simp) (fun S => (Polynomial.X : Polynomial ℝ) ^ S.card)]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : StrongIndependent H S <;> by_cases hr : r ∈ S <;> simp [hS, hr]

end ResearchMain.Hypercomb
