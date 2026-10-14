import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

namespace ResearchMain.SIBO

noncomputable def rationalCircleToRealCircle :
    AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ))
    (AddSubgroup.zmultiples (1 : ℝ)) (Rat.castHom ℝ).toAddMonoidHom (by
      intro q hq
      change (q : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ)
      rcases AddSubgroup.mem_zmultiples_iff.mp hq with ⟨n, hn⟩
      apply AddSubgroup.mem_zmultiples_iff.mpr
      refine ⟨n, ?_⟩
      simp only [zsmul_eq_mul, mul_one] at hn ⊢
      exact_mod_cast hn)

theorem rationalCircleToRealCircle_injective :
    Function.Injective rationalCircleToRealCircle := by
  apply (injective_iff_map_eq_zero rationalCircleToRealCircle).2
  intro x
  refine Quotient.inductionOn x ?_
  intro q hq
  change ((q : ℝ) : AddCircle (1 : ℝ)) = 0 at hq
  apply (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr
  rcases (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hq with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simp only [zsmul_eq_mul, mul_one] at hn ⊢
  exact_mod_cast hn

noncomputable def rationalCircleChar : AddChar (AddCircle (1 : ℚ)) ℂ :=
  (Circle.coeHom.compAddChar AddCircle.toCircle_addChar).compAddMonoidHom
    rationalCircleToRealCircle

theorem rationalCircleChar_injective : Function.Injective rationalCircleChar := by
  exact Subtype.coe_injective.comp
    ((AddCircle.injective_toCircle one_ne_zero).comp rationalCircleToRealCircle_injective)

/-- Complex-valued characters separate every nonzero element of every abelian group. -/
theorem exists_separating_character {A : Type*} [AddCommGroup A] {a : A} (ha : a ≠ 0) :
    ∃ χ : AddChar A ℂ, χ a ≠ 1 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  refine ⟨rationalCircleChar.compAddMonoidHom c, ?_⟩
  intro heq
  apply hc
  apply rationalCircleChar_injective
  change rationalCircleChar (c a) = 1 at heq
  simpa only [AddChar.map_zero_eq_one] using heq

end ResearchMain.SIBO
