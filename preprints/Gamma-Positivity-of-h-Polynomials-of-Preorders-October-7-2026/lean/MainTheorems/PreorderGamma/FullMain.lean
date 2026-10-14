import MainTheorems.PreorderGamma.RootRealization
import MainTheorems.PreorderGamma.RootDimension
import MainTheorems.PreorderGamma.RootDecomposition
import MainTheorems.PreorderGamma.RootDuality
import MainTheorems.PreorderGamma.MacaulayNumerical.PreorderGVector
import MainTheorems.PreorderGamma.Macaulay.Multicomplex

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem preorder_gamma_full_main :
    Module.finrank ℝ (affineSpan ℝ (rootPolytope (E := E))).direction =
        2 * Fintype.card E ∧
      rootHStar (E := E) = (supportPolynomial (E := E)).map (Nat.castRingHom ℚ) ∧
      supportPolynomial (E := E) =
        ∑ k ∈ Finset.range (Fintype.card E / 2 + 1),
          Polynomial.C (gammaCoefficient (E := E) k) * Polynomial.X ^ k *
            (1 + Polynomial.X) ^ (Fintype.card E - 2 * k) ∧
      (∀ t : ℕ, rootLatticeCount (E := E) t =
        ∑ k ∈ Finset.range (Fintype.card E + 1),
          (supportPolynomial (E := E)).coeff k *
            Nat.choose (2 * Fintype.card E + t - k) (2 * Fintype.card E)) ∧
      (∃ height : SimplicialRealization.QuotientIndex E → ℝ,
        (∀ v, 0 < height v) ∧
          Module.finrank ℝ
            (affineSpan ℝ (SimplicialRealization.projectivePolytope height)).direction =
              Fintype.card E ∧
          SimplicialRealization.HasSimplicialBoundary height ∧
          (SimplicialRealization.boundaryHPolynomial height).map (Int.castRingHom ℚ) =
            rootHStar (E := E)) ∧
      supportGVector (E := E) 0 = 1 ∧
      (∀ d : ℕ, 0 < d → supportGVector (E := E) (d + 1) ≤
        MacaulayNumerical.macaulayRaise d (supportGVector (E := E) d)) := by
  exact ⟨rootPolytope_dimension, root_hStar_support, preorder_gamma_expansion,
    root_lattice_count_binomial, preorder_root_hStar_simplicial_realization,
    MacaulayNumerical.preorder_g_macaulay_conditions⟩

theorem preorder_root_integer_decomposition (t : ℕ)
    (z : (Option E → ℤ) × (Option E → ℤ)) (hz : RootIntegerPoints t z) :
    ∃ f : Fin t → AugmentedEdge E,
      z = ∑ i : Fin t, integerRootVertex (f i).val.1 (f i).val.2 :=
  root_integer_decomposition t z hz

theorem preorder_root_orderDual_count (t : ℕ) :
    rootLatticeCount (E := E) t = rootLatticeCount (E := OrderDual E) t :=
  root_lattice_count_orderDual t

theorem preorder_root_g_multicomplex :
    ∃ C : Macaulay.FiniteMulticomplex (Macaulay.FaceVertex E),
      ∀ i : ℕ, (C.hilbert i : ℚ) = rootTruncatedGVector (E := E) i := by
  obtain ⟨C, hC⟩ := Macaulay.preorder_g_multicomplex (E := E)
  refine ⟨C, fun i => ?_⟩
  rw [hC i, rootTruncatedGVector_eq_support]

end ResearchMain.PreorderGamma
