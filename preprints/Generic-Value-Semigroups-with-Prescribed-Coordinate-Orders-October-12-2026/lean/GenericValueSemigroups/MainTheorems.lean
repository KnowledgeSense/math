import GenericValueSemigroups.GenericSemigroup
import GenericValueSemigroups.Multiplicity
import GenericValueSemigroups.ArithmeticProgression

namespace GenericValueSemigroups
open scoped BigOperators Classical

/-- The full generic formal value theorem, with a finite nonzero integer condition
at the actual conductor plus the smallest coordinate order. -/
theorem generic_value_semigroup_theorem {d : ℕ} (hd : 2≤d) (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) :
    ∃ (C : ℕ) (i : Fin d) (P : MvPolynomial (JetVariable d (C+r i)) ℤ),
      (∀ j,r i≤r j) ∧ P≠0 ∧
      (∀ N,(∀ n,N≤n → n∈Set.range (greedy (weightAt r hr (by omega)))) ↔ C≤N) ∧
      (∀ f : Fin d → PowerSeries ℂ,
        (∀ j,PowerSeries.order (f j)=r j) →
        (∀ j,PowerSeries.coeff (r j) (f j)=1) →
        jetEvaluation (jetAssignment f r (C+r i)) P≠0 →
        formalValues f=Set.range (greedy (weightAt r hr (by omega)))) ∧
      (∃ f : Fin d → PowerSeries ℂ,
        (∀ j,PowerSeries.order (f j)=r j) ∧
        (∀ j,PowerSeries.coeff (r j) (f j)=1) ∧
        formalValues f=Set.range (greedy (weightAt r hr (by omega)))) := by
  obtain ⟨i,hmin⟩ := exists_minimum_coordinate r (by omega)
  let a : Fin d := ⟨0,by omega⟩
  let b : Fin d := ⟨1,by omega⟩
  have hab : a≠b := by intro h; have hh := congrArg Fin.val h; simp [a,b] at hh
  obtain ⟨D,C,gaps,_,_,hC,_⟩ := greedy_genus_conductor r hr (by omega) a b hab
  have ht := (hC C).mpr le_rfl
  refine ⟨C,i,genericJetCondition r hr (by omega) (C+r i),hmin,
    genericJetCondition_ne_zero r hr (by omega) (C+r i),hC,?_,?_⟩
  · intro f hf hl hp
    exact generic_formal_values_eq f r hr (by omega) hf hl i C ht hp
  · exact exists_family_generic_formal_values r hr (by omega) i C ht

/-- The greedy set is an actual cofinite additive submonoid, established through
its realization as a formal value semigroup. -/
theorem greedy_numerical_semigroup {d : ℕ} (hd : 2≤d) (r : Fin d → ℕ)
    (hr : ∀ i,0<r i) :
    ∃ S : AddSubmonoid ℕ, (S : Set ℕ)=Set.range (greedy (weightAt r hr (by omega))) ∧
      (Set.range (greedy (weightAt r hr (by omega))))ᶜ.Finite := by
  obtain ⟨_,_,_,_,_,_,_,f,hf,_,hG⟩ := generic_value_semigroup_theorem hd r hr
  have hzero : ∀ i,(f i).constantCoeff=0 := by
    intro i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    apply PowerSeries.coeff_of_lt_order
    rw [hf]
    exact_mod_cast hr i
  refine ⟨formalValueSubmonoid f hzero,hG,?_⟩
  let a : Fin d := ⟨0,by omega⟩
  let b : Fin d := ⟨1,by omega⟩
  have hab : a≠b := by intro h; have hh := congrArg Fin.val h; simp [a,b] at hh
  obtain ⟨_,_,gaps,hg,_⟩ := greedy_genus_conductor r hr (by omega) a b hab
  have he : (Set.range (greedy (weightAt r hr (by omega))))ᶜ=(gaps : Set ℕ) := by
    ext n; exact (hg n).symm
  rw [he]
  exact gaps.finite_toSet

/-- Every prescribed coordinate order belongs to the generic value semigroup. -/
theorem coordinate_mem_greedy {d : ℕ} (hd : 2≤d) (r : Fin d → ℕ)
    (hr : ∀ i,0<r i) (i : Fin d) :
    r i ∈ Set.range (greedy (weightAt r hr (by omega))) := by
  obtain ⟨_,_,_,_,_,_,_,f,hf,_,hG⟩ := generic_value_semigroup_theorem hd r hr
  rw [← hG]
  refine ⟨(MvPolynomial.X i : MvPolynomial (Fin d) ℂ).toMvPowerSeries,?_⟩
  simpa only [MvPowerSeries.subst_coe,MvPolynomial.aeval_X] using hf i

/-- Exact genus and conductor formulas, with signed deficits and a uniform finite cutoff. -/
theorem genus_conductor_formula {d : ℕ} (hd : 2≤d) (r : Fin d → ℕ)
    (hr : ∀ i,0<r i) (a b : Fin d) (hab : a≠b) :
    ∃ (g C J : ℕ) (gaps : Finset ℕ),
      (∀ n,n∈gaps ↔ n∉Set.range (greedy (weightAt r hr (by omega)))) ∧
      gaps.card=g ∧
      (∀ N,(∀ n,N≤n → n∈Set.range (greedy (weightAt r hr (by omega)))) ↔ C≤N) ∧
      (C : ℤ)-(weightCount r C : ℤ)=(g : ℤ) ∧
      (∀ n : ℕ,(n : ℤ)-(weightCount r n : ℤ)≤g) ∧
      (∀ n,n<C → (n : ℤ)-(weightCount r n : ℤ)<g) ∧
      (weightAt r hr (by omega) J : ℤ)-(J : ℤ)=(g : ℤ) ∧
      (∀ j : ℕ,(weightAt r hr (by omega) j : ℤ)-(j : ℤ)≤g) ∧
      C<4*r a*r b ∧
      (∀ n,4*r a*r b≤n → (n : ℤ)-(weightCount r n : ℤ)≤0) := by
  obtain ⟨D,J,h,hJ,hmin⟩ := exists_first_weight_deficit_maximum r hr (by omega) a b hab
  obtain ⟨gaps,hg,hcard⟩ := greedy_gaps_finite_card (weightAt r hr (by omega)) D J h hJ
  obtain ⟨hs,hsb,hsfirst⟩ := signed_count_deficit_maximum r hr (by omega) D J h hJ hmin
  refine ⟨D,J+D,J,gaps,hg,hcard,?_,hs,hsb,hsfirst,?_,?_,?_,?_⟩
  · exact greedy_conductor _ (weightAt_zero r hr (by omega)) D J h hJ hmin
  · have hh : (weightAt r hr (by omega) J : ℤ)=(J : ℤ)+D := by exact_mod_cast hJ
    omega
  · intro j
    have hh : (weightAt r hr (by omega) j : ℤ)≤(j : ℤ)+D := by exact_mod_cast h j
    omega
  · exact conductor_lt_two_coordinate_cutoff r hr (by omega) D J h hJ hmin a b hab
  · intro n hn
    have hh := weightCount_ge_above_cutoff r hr a b hab hn
    omega

/-- The multiplicity lower bound and the full minimal-generator cutoff. -/
theorem genus_and_minimal_generators {d : ℕ} (hd : 2≤d) (r : Fin d → ℕ)
    (hr : ∀ i,0<r i) (i : Fin d) (hmin : ∀ j,r i≤r j) (hm : 2≤r i)
    (gaps : Finset ℕ)
    (hg : ∀ n,n∈gaps ↔ n∉Set.range (greedy (weightAt r hr (by omega))))
    (C : ℕ) (hC : ∀ n,C≤n → n∈Set.range (greedy (weightAt r hr (by omega)))) :
    r i-1≤gaps.card ∧
      ∀ n,IsMinimalGenerator (Set.range (greedy (weightAt r hr (by omega)))) n → n<C+r i := by
  refine ⟨greedy_genus_ge_minimum_sub_one r hr (by omega) (r i) (hr i) hmin gaps hg,?_⟩
  have hCp : 0<C := by
    by_contra hz
    have h1 := hC 1 (by omega)
    exact no_positive_greedy_below_minimum r hr (by omega) (r i) (hr i) hmin 1
      (by omega) (by omega) h1
  exact minimal_generator_lt_conductor_add _ C (r i) hCp (hr i)
    (coordinate_mem_greedy hd r hr i) hC

end GenericValueSemigroups
