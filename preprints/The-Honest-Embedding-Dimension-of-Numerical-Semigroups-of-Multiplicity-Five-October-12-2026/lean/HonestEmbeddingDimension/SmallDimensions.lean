import HonestEmbeddingDimension.MaximalDimension

namespace HonestEmbeddingDimension

/-- A nontrivial numerical multiplicity cannot be realized in one analytic coordinate. -/
theorem analytic_dimension_ge_two {S : NumericalSemigroup} {e : ℕ}
    (hm : HasMultiplicity S 5) (hreal : AnalyticallyRealizes S e) : 2 ≤ e := by
  let a := S.firstNonmultiple 5 (by omega)
  obtain ⟨haS,ha⟩ := S.firstNonmultiple_spec 5 (by omega)
  have ha0 : 0<a := by
    by_contra hn
    have hz : a=0 := by omega
    exact ha (by simpa [a] using (show 5 ∣ a by rw [hz]; exact dvd_zero 5))
  cases e with
  | zero => exact False.elim (no_zero_dimensional_realization hm hreal)
  | succ e =>
    obtain ⟨f,hf,hfS⟩ := parameterized_normal_form hm ha0 haS ha
      (by intro n hn hnd; exact NumericalSemigroup.firstNonmultiple_le hn hnd) hreal.formal
    have hares : a%5 ≠ 0 := fun hmod => ha (Nat.dvd_of_mod_eq_zero hmod)
    apply linear_low_residue_bound (m := 5) (a := a) (N := 2*a) (by omega) f hf le_rfl
      (![0,a] : Fin 2 → ℕ) (by intro i; fin_cases i <;> dsimp <;> omega)
    · intro i j hij
      fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;> first | rfl | omega
    · intro i
      rw [hfS]
      fin_cases i
      · exact S.monoid.zero_mem
      · exact haS

theorem formalValues_reorder_two (f : Fin 2 → PowerSeries ℂ)
    (hf0 : ∀ i, (f i).constantCoeff=0) (i j : Fin 2) (hij : i ≠ j) :
    formalValues ![f i,f j] = formalValues f := by
  let e : Fin 2 → Fin 2 := ![i,j]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e,eq_comm]
  have hs := Finite.surjective_of_injective he
  have h0 : ∀ a, ((![f i,f j] : Fin 2 → PowerSeries ℂ) a).constantCoeff=0 := by
    intro a; fin_cases a <;> simp [hf0]
  rw [formalValues_eq_polynomialValues _ h0,formalValues_eq_polynomialValues _ hf0]
  apply polynomialValues_eq_of_coordinateAlgebra_eq
  have hh : (![f i,f j] : Fin 2 → PowerSeries ℂ) = f ∘ e := by
    funext a; fin_cases a <;> rfl
  rw [hh,coordinateAlgebra,hs.range_comp f]
  rfl

/-- Every two-dimensional analytic realization has the genuine two-generator value semigroup. -/
theorem two_dimensional_semigroup_is_pair {S : NumericalSemigroup}
    (hm : HasMultiplicity S 5) (hreal : AnalyticallyRealizes S 2) :
    ∃ a, 0<a ∧ S.monoid = generatedPair 5 a := by
  let a := S.firstNonmultiple 5 (by omega)
  obtain ⟨haS,ha⟩ := S.firstNonmultiple_spec 5 (by omega)
  have ha0 : 0<a := by
    by_contra hn
    have hz : a=0 := by omega
    exact ha (by simpa [a] using (show 5 ∣ a by rw [hz]; exact dvd_zero 5))
  obtain ⟨f,hf0,hfS⟩ := hreal.formal
  have hmem (n : ℕ) : n ∈ formalValues f ↔ n ∈ S.monoid := by rw [hfS]; rfl
  obtain ⟨g,i,j,hg0,hgv,hij,hgi,hgj⟩ := formal_two_coordinate_normal_form f hf0 5 a (by omega) ha0
    ((hmem 5).mpr hm.2.1) (by intro n hn; exact hm.2.2 n ((hmem n).mp hn))
    ((hmem a).mpr haS) ha (by intro n hn hnd; exact NumericalSemigroup.firstNonmultiple_le ((hmem n).mp hn) hnd)
  have hperm := formalValues_reorder_two g hg0 i j hij
  have he : (![g i,g j] : Fin 2 → PowerSeries ℂ) = planeCoordinates 5 (g j) := by
    funext k; fin_cases k <;> simp [planeCoordinates,hgi]
  rw [he] at hperm
  have hvS := hperm.trans (hgv.trans hfS)
  refine ⟨a,ha0,?_⟩
  apply SetLike.coe_injective
  exact hvS.symm.trans (formal_plane_values 5 a (by omega) ha0 (S.firstNonmultiple_coprime_five) (g j) hgj)

theorem embeddingDimension_le_two_of_analytic_two {S : NumericalSemigroup}
    (hm : HasMultiplicity S 5) (hreal : AnalyticallyRealizes S 2) : S.embeddingDimension ≤ 2 := by
  obtain ⟨a,_,hpair⟩ := two_dimensional_semigroup_is_pair hm hreal
  have hG : ({5,a} : Set ℕ) ⊆ S.monoid := by
    intro n hn
    rw [hpair,generatedPair_eq_closure]
    exact AddSubmonoid.subset_closure hn
  have hsub : S.minimalGenerators ⊆ ({5,a} : Set ℕ) := by
    intro n hn
    apply NumericalSemigroup.minimalGenerator_mem_of_mem_closure hG hn
    rw [← generatedPair_eq_closure,← hpair]
    exact hn.2.1
  have hh := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hp : ({5,a} : Set ℕ).ncard ≤ 2 := by
    by_cases h : 5 = a
    · simp [h]
    · rw [Set.ncard_pair h]
  exact hh.trans hp

theorem analytic_dimension_ge_three_of_embeddingDimension {S : NumericalSemigroup} {e : ℕ}
    (hm : HasMultiplicity S 5) (hE : 3 ≤ S.embeddingDimension)
    (hreal : AnalyticallyRealizes S e) : 3 ≤ e := by
  have htwo := analytic_dimension_ge_two hm hreal
  by_contra hn
  have he : e=2 := by omega
  subst e
  have hdim := embeddingDimension_le_two_of_analytic_two hm hreal
  omega

theorem honest_dimension_two_of_embeddingDimension {S : NumericalSemigroup}
    (hm : HasMultiplicity S 5) (hE : S.embeddingDimension=2) : HasHonestEmbeddingDimension S 2 := by
  have hreal := analytic_realization_embeddingDimension hm
  rw [hE] at hreal
  exact ⟨hreal,fun _ he => analytic_dimension_ge_two hm he⟩

theorem honest_dimension_three_of_embeddingDimension {S : NumericalSemigroup}
    (hm : HasMultiplicity S 5) (hE : S.embeddingDimension=3) : HasHonestEmbeddingDimension S 3 := by
  have hreal := analytic_realization_embeddingDimension hm
  rw [hE] at hreal
  exact ⟨hreal,fun _ he => analytic_dimension_ge_three_of_embeddingDimension hm (by omega) he⟩

end HonestEmbeddingDimension
