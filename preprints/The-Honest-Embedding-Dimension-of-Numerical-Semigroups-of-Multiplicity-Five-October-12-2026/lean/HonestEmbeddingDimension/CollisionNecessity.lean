import HonestEmbeddingDimension.FirstCollision
import HonestEmbeddingDimension.IntrinsicNormalForm

namespace HonestEmbeddingDimension

theorem residue_injective_below_firstCollision (a b : ℕ) :
    ∀ p q p' q' : ℕ, a*p+b*q < firstCollision a b → a*p'+b*q' < firstCollision a b →
      (a*p+b*q)%5=(a*p'+b*q')%5 → p=p' ∧ q=q' := by
  have step : ∀ p q p' q' : ℕ, a*p+b*q ≤ a*p'+b*q' → a*p'+b*q' < firstCollision a b →
      (a*p+b*q)%5=(a*p'+b*q')%5 → p=p' ∧ q=q' := by
    intro p q p' q' hle hlt hmod
    by_contra hne
    obtain ⟨x,hx⟩ := (Nat.modEq_iff_dvd' hle).mp hmod
    have hsum := Nat.sub_add_cancel hle
    rw [hx] at hsum
    have hfac : HasTwoFactorizations a b (a*p'+b*q') := by
      refine ⟨x,p,q,0,p',q',?_,?_,?_⟩
      · omega
      · omega
      · tauto
    have hfirst := firstCollision_le hfac
    omega
  intro p q p' q' hlt hlt' hmod
  rcases le_total (a*p+b*q) (a*p'+b*q') with hle | hle
  · exact step p q p' q' hle hlt' hmod
  · obtain ⟨hp,hq⟩ := step p' q' p q hle hlt hmod.symm
    exact ⟨hp.symm,hq.symm⟩

theorem HasFourGenerators.analytic_dimension_ge_three {S : NumericalSemigroup} {a b c e : ℕ}
    (h : HasFourGenerators S a b c) (hm : HasMultiplicity S 5)
    (hreal : AnalyticallyRealizes S e) : 3 ≤ e := by
  obtain ⟨ha,hmina,hb,hminb,_,_⟩ := h.normalization_data hm
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  exact analytic_characteristic_dimension_ge_three hm (by omega) (by omega)
    (NumericalSemigroup.minimalGenerator_coprime_five hm h.minimal.2.1 (by omega)).symm
    h.minimal.2.1.2.1 h.minimal.2.2.1.2.1 ha hmina hb hminb hreal

theorem HasFiveGenerators.analytic_dimension_ge_three {S : NumericalSemigroup} {a b c d e : ℕ}
    (h : HasFiveGenerators S a b c d) (hm : HasMultiplicity S 5)
    (hreal : AnalyticallyRealizes S e) : 3 ≤ e := by
  obtain ⟨ha,hmina,hb,hminb,_,_⟩ := h.normalization_data hm
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  exact analytic_characteristic_dimension_ge_three hm (by omega) (by omega)
    (NumericalSemigroup.minimalGenerator_coprime_five hm h.minimal.2.1 (by omega)).symm
    h.minimal.2.1.2.1 h.minimal.2.2.1.2.1 ha hmina hb hminb hreal

/-- Necessity of the exact first-collision inequality for every original analytic realization. -/
theorem four_generator_collision_necessary {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hreal : AnalyticallyRealizes S 3) : firstCollision a b < c := by
  obtain ⟨ha,hmina,hb,hminb,hcnew,_⟩ := h.normalization_data hm
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  obtain ⟨Y,Z,hY,hZ,hvalues⟩ := analytic_characteristic_triple hm (by omega) (by omega)
    (NumericalSemigroup.minimalGenerator_coprime_five hm h.minimal.2.1 (by omega)).symm
    h.minimal.2.1.2.1 h.minimal.2.2.1.2.1 ha hmina hb hminb hreal
  have hf0 : ∀ i, (tripleCoordinates 5 Y Z i).constantCoeff=0 := by
    intro i
    fin_cases i
    · simp [tripleCoordinates]
    · apply PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
      change (1 : ℕ∞) ≤ Y.order
      rw [hY]; exact_mod_cast (show 1 ≤ a by omega)
    · apply PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
      change (1 : ℕ∞) ≤ Z.order
      rw [hZ]; exact_mod_cast (show 1 ≤ b by omega)
  apply new_triple_value_gt_collision 5 a b (firstCollision a b) c (by omega) (by omega) (by omega)
    Y Z hY hZ (residue_injective_below_firstCollision a b) (firstCollision_representation a b)
  · rw [← formalValues_eq_polynomialValues _ hf0,hvalues]
    exact h.minimal.2.2.2.2.1
  · exact hcnew

end HonestEmbeddingDimension
