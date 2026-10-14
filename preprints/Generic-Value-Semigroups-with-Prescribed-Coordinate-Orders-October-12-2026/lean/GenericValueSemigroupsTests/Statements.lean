import GenericValueSemigroups

namespace GenericValueSemigroups.Tests

#check release_generic_value_theorem
#check release_algebraically_independent_values
#check greedy_numerical_semigroup
#check genus_conductor_formula
#check genus_and_minimal_generators
#check greedy_range_eq_univ_iff
#check arithmetic_progression_genus_bounds
#check even_arithmetic_progression_genus_bigO

example {d : ℕ} (hd : 2 ≤ d) (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (a : Fin d → ℕ → ℂ)
    (ha : AlgebraicIndependent ℚ (fun v : Fin d × ℕ => a v.1 (v.2+1))) :
    formalValues (normalizedFamily r a)=Set.range (greedy (weightAt r hr (by omega))) :=
  release_algebraically_independent_values hd r hr a ha

example {d : ℕ} (hd : 2 ≤ d) (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (gaps : Finset ℕ)
    (hg : ∀ n, n ∈ gaps ↔ n ∉ Set.range (greedy (weightAt r hr (by omega)))) :
    ((d-1 : ℕ) : ℝ)/(d : ℝ)*genusScale r-(∑ i, (r i : ℝ))-1 ≤ (gaps.card : ℝ) ∧
      (gaps.card : ℝ) ≤ ((d-1 : ℕ) : ℝ)/(d : ℝ)*genusScale r :=
  greedy_genus_asymptotic hd r hr gaps hg

end GenericValueSemigroups.Tests
