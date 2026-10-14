# Embedding-dimension strata

Lean formalization of the [manuscript](../article.pdf), for Γ = ⟨10,11,34,46,58⟩.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build EmbeddingDimensionStrata
lake script run audit EmbeddingDimensionStrata
lake env leanchecker --fresh EmbeddingDimensionStrata
```

The shared toolchain and dependency revisions are pinned at the repository root.

## Main statements

- **Actual objects:** `completeGammaParameterEquiv` identifies arbitrary closed power-series subalgebras with value semigroup Γ with the genuine finite-jet parameter locus. `parameter_condition_iff_equations` proves the exact five equations in both directions.
- **Theorems affine and coords:** `parameterAffineEquiv`, its `polynomial` and `inverse_polynomial` lemmas, `parameterCoordinateRingEquiv`, and `affineSchemeIso` establish the polynomial coordinate isomorphisms A⁵⁴ × A³ and A⁵⁷. `originalEquationRemainder_triangular` proves triangularity in the paper's original order. `solvedGraphPolynomial_baseChange_weighted` and `parameter_condition_iff_polynomial_graph` prove the homogeneous graph statement. `remainingCoordinate_description` identifies precisely the paper's 54 retained coefficients. A, B, C are actual reduced relation coefficients.
- **Theorem main:** `main_rank_and_generators` proves the actual cotangent dimension and minimum algebra-generator number are 5 − rank [[A,C],[0,B]]. `main_complete_rank_and_generators` proves the corresponding statement for the complete algebra's own cotangent module and minimum topological-generator number.
- **Strata:** `exact_strata`, `generatorStratum_two_eq_empty`, `generatorStratum_three_coordinates`, `generatorStratum_four_coordinates`, and `generatorStratum_five_eq_univ` give the exact and at-most loci. `four_generator_scheme_membership` and `parameterFourStratumSchemeIso` connect the true four-generator locus to its open subscheme and punctured-product model.
- **Theorem q47:** `question47` excludes every fixed polynomial reduction detector and one/two principal opens defined by arbitrary elements of the actual coordinate ring. `generatorStratum_four_minimal_regular_cover` proves that exactly three regular principal opens suffice. Reduction is defined by the increasing positive-order monomial algorithm for ⟨10,11,34,46⟩.
- **Theorem q48:** `question48` proves non-affineness, non-isomorphism to the proposed product, simple connectivity, and non-homeomorphism. `parameterFour_canonical_regularFunctionsEquiv` and `parameterFour_units_are_constant_sections` identify its actual structure-sheaf section ring and units via canonical restriction and scalar sections.

Algebraic results are proved over the indicated arbitrary fields or rings; the obstruction and classical-topology statements specialize to ℂ. For complete power-series algebras the coefficient field is discrete, so the coefficient-product topology is the formal t-adic topology. Separately, the complex parameter variety uses its ordinary coefficient-subspace topology. The homeomorphism is proved continuous in that topology, rather than used to define it.

`Examples.lean` checks genuine parameter points of embedding dimensions 3, 4, and 5, as well as the polynomial obstruction and simple connectivity.
