import FourGeneratedSemigroups.TopSlice
import FourGeneratedSemigroups.StaircaseFiniteness
import Mathlib.Order.Preorder.Finite

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

/-- Coordinate-maximal staircase monomials are maximal for divisibility. -/
theorem corner_maximal (a : Factorization) (ha : a∈staircaseCorners G)
    (b : Factorization) (hb : b∈staircase G) (hab : a≤b) : a=b := by
  ext i
  have hle := hab i
  by_contra hne
  have hi : i≠0 := by intro he; subst i; exact hne (ha.1.1.trans hb.1.symm)
  have hstep : a+Finsupp.single i 1≤b := by
    intro j
    by_cases hj : j=i
    · subst j; simp only [Finsupp.add_apply,Finsupp.single_eq_same]; omega
    · simpa [Finsupp.single_apply,hj] using hab j
  exact ha.2 i hi (staircase_lower G hb hstep)

theorem exists_corner_above (a : Factorization) (ha : a∈staircase G) :
    ∃ b∈staircaseCorners G,a≤b := by
  obtain ⟨b,hab,hb,hmax⟩ := (finite_staircase G).exists_le_maximal ha
  refine ⟨b,⟨hb,?_⟩,hab⟩
  intro i hi hstep
  have hle : b≤b+Finsupp.single i 1 := le_add_of_nonneg_right (zero_le)
  have hh := hmax hstep hle
  have hcoord := hh i
  simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hcoord
  omega

/-- On a horizontal slice, distinct staircase corners have distinct first coordinates. -/
theorem corner_eq_of_first_eq (a b : Factorization)
    (ha : a∈staircaseCorners G) (hb : b∈staircaseCorners G)
    (hz : a 3=b 3) (hx : a 1=b 1) : a=b := by
  by_cases hy : a 2≤b 2
  · apply corner_maximal G a ha b hb.1
    intro i; fin_cases i <;> simp_all [ha.1.1,hb.1.1]
  · symm
    apply corner_maximal G b hb a ha.1
    intro i; fin_cases i <;> simp_all [ha.1.1,hb.1.1] ; omega

theorem corner_eq_of_second_eq (a b : Factorization)
    (ha : a∈staircaseCorners G) (hb : b∈staircaseCorners G)
    (hz : a 3=b 3) (hy : a 2=b 2) : a=b := by
  by_cases hx : a 1≤b 1
  · apply corner_maximal G a ha b hb.1
    intro i; fin_cases i <;> simp_all [ha.1.1,hb.1.1]
  · symm
    apply corner_maximal G b hb a ha.1
    intro i; fin_cases i <;> simp_all [ha.1.1,hb.1.1] ; omega

theorem corner_second_reverse (a b : Factorization)
    (ha : a∈staircaseCorners G) (hb : b∈staircaseCorners G)
    (hz : a 3=b 3) (hx : a 1<b 1) : b 2<a 2 := by
  by_contra hy
  have he : a=b := corner_maximal G a ha b hb.1 (by
    intro i; fin_cases i <;> simp_all [ha.1.1,hb.1.1] ; omega)
  have := congrArg (fun c : Factorization => c 1) he
  omega

end FourGeneratedSemigroups
