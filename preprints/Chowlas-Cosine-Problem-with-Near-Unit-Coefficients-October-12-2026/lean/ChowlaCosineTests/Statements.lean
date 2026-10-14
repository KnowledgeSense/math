import ChowlaCosine

namespace ChowlaCosine.Tests

theorem original_integer_statement {N : ℕ} {a : Fin N → ℤ} (s : Fin N → ℝ)
    (hN : 1 ≤ N) (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j)
    (hcoeff : ∀ j, s j ∈ Set.Icc (0.99 : ℝ) 1.01) :
    ∃ x : ℝ, (∑ j, s j * Real.cos (2 * Real.pi * (a j : ℝ) * x)) ≤
      -(N : ℝ) ^ (1 / 9 : ℝ) / 20 :=
  chowla_cosine_main s hN hinj hpos hcoeff

theorem original_natural_statement {N : ℕ} {a : Fin N → ℕ} (s : Fin N → ℝ)
    (hN : 1 ≤ N) (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j)
    (hcoeff : ∀ j, s j ∈ Set.Icc (0.99 : ℝ) 1.01) :
    ∃ x : ℝ, (∑ j, s j * Real.cos (2 * Real.pi * (a j : ℝ) * x)) ≤
      -(N : ℝ) ^ (1 / 9 : ℝ) / 20 :=
  chowla_cosine_main_nat s hN hinj hpos hcoeff

theorem attained_cosine_minimum {N : ℕ} {a : Fin N → ℤ} (s : Fin N → ℝ)
    (hN : 1 ≤ N) (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j)
    (hcoeff : ∀ j, s j ∈ Set.Icc (0.99 : ℝ) 1.01) :
    ∃ x₀ ∈ Set.Ico (0 : ℝ) 1,
      cosineSum a s x₀ ≤ -(N : ℝ) ^ (1 / 9 : ℝ) / 20 ∧
      ∀ x : ℝ, cosineSum a s x₀ ≤ cosineSum a s x :=
  chowla_cosine_minimum s hN hinj hpos hcoeff

end ChowlaCosine.Tests
