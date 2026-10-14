import HonestEmbeddingDimension.GeometricValues
import HonestEmbeddingDimension.DoubleGeometricValues
import HonestEmbeddingDimension.ClassificationArithmetic

namespace HonestEmbeddingDimension

/-- Source case 4A has a genuine three-dimensional convergent realization. -/
theorem analytic_realization_case_4A {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (2*a)%5) (hc : c % 5 = (3*a)%5) (hca : 2*a < c) :
    AnalyticallyRealizes S 3 := by
  have ha0 : 0 < a := by have := h.five_lt_a; omega
  have hb0 : 0 < b := by have := h.a_lt_b; omega
  obtain ⟨hδ,_,_,hu,hv,_,hZZ⟩ := four_generator_parameters_4A h hb hc hca
  have hcond := (four_generator_conductor_4A hm h hb hc hca).2
  refine ⟨fun t : ℂ => ![t^5,t^a,t^b/(1-t^(c-2*a))],?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact analyticAt_id.pow 5
    · exact analyticAt_id.pow a
    · exact analyticAt_geometric_quotient b (c-2*a) hδ
  · simp [Nat.ne_of_gt ha0,Nat.ne_of_gt hb0]
  · apply analytic_geometric_values S.monoid 5 a b c (c-2*a) ((2*a-b)/5) ((a+b-c)/5)
      (min (a+c) (2*b)) (by omega) ha0 hb0 hδ hu (by omega) hv hZZ (min_le_left _ _)
      (le_trans (min_le_left _ _) (by have := h.a_lt_b; omega)) h.generates
      (four_generator_basis_residues_injective hm h)
    intro n hn
    apply S.mem_of_conductor_le
    rw [hcond]
    omega

/-- The positive five-generator case has the explicit convergent three-coordinate realization. -/
theorem analytic_realization_five_positive {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d)
    (hb : b % 5 = (2*a)%5) (hc : c % 5 = (3*a)%5) (hd : d % 5 = (4*a)%5)
    (hc2 : 2*a < c) (hdab : a+b < d) : AnalyticallyRealizes S 3 := by
  have ha0 : 0 < a := by have := h.five_lt_a; omega
  have hb0 : 0 < b := by have := h.a_lt_b; omega
  obtain ⟨hδ,hε,_,_,hu,hv,hZZ,hYW⟩ := five_generator_positive_parameters h hb hc hd hc2 hdab
  have hcond := (five_generator_aperyMax_conductor hm h hb hc hd).2
  refine ⟨fun t : ℂ => ![t^5,t^a,t^b*(1+t^((c-2*a)+(d-a-b)))/(1-t^(c-2*a))],?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact analyticAt_id.pow 5
    · exact analyticAt_id.pow a
    · exact analyticAt_double_geometric b (c-2*a) (d-a-b) hδ
  · simp [Nat.ne_of_gt ha0,Nat.ne_of_gt hb0]
  · apply analytic_double_geometric_values S.monoid 5 a b c d (c-2*a) (d-a-b)
      ((2*a-b)/5) ((a+b-c)/5) (by omega) ha0 hb0 hδ hε hu (by omega) hv (by omega)
      hZZ.le hYW.le (by have := h.a_lt_b; omega) h.generates
      (five_generator_first_four_residues_injective hm h)
    intro n hn
    apply S.mem_of_conductor_le
    rw [hcond]
    omega

end HonestEmbeddingDimension
