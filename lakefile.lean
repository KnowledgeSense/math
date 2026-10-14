import Lake
open Lake DSL

package math where
  weakLeanArgs := #["-j1"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

@[default_target]
lean_lib LocalPermutation where
  srcDir := "preprints/Local-Permutation-Polynomials-of-Maximum-Degree-with-Coefficients-in-the-Prime-Field-October-7-2026/lean"
  roots := #[`LocalPermutation, `MainTheorems.LocalPermutation]
  globs := #[`LocalPermutation, `MainTheorems.LocalPermutation.+]

@[default_target]
lean_lib Chores where
  srcDir := "preprints/EFX-Allocations-of-Chores-That-Are-Cheap-for-Exactly-Two-Agents-October-7-2026/lean"
  roots := #[`Chores, `MainTheorems.Chores]
  globs := #[`Chores, `MainTheorems.Chores.+]

@[default_target]
lean_lib PreorderGamma where
  srcDir := "preprints/Gamma-Positivity-of-h-Polynomials-of-Preorders-October-7-2026/lean"
  roots := #[`PreorderGamma, `MainTheorems.PreorderGamma, `MainTheorems.PreorderReciprocity]
  globs := #[`PreorderGamma, `MainTheorems.PreorderGamma.+, `MainTheorems.PreorderReciprocity.+]

@[default_target]
lean_lib Laminar where
  srcDir := "preprints/Cyclic-Orderings-of-Laminar-Matroids-with-Prescribed-Basis-Intervals-October-8-2026/lean"
  roots := #[`Laminar, `MainTheorems.Laminar]
  globs := #[`Laminar, `MainTheorems.Laminar.+]

@[default_target]
lean_lib DiagonalSchatten where
  srcDir := "preprints/Schatten-Norm-Compression-for-2-by-N-Block-Matrices-with-Diagonal-Blocks-October-8-2026/lean"
  roots := #[`DiagonalSchatten, `MainTheorems.DiagonalSchatten]
  globs := #[`DiagonalSchatten, `MainTheorems.DiagonalSchatten.+]

@[default_target]
lean_lib WishartBlocks where
  srcDir := "preprints/The-Gaussian-Product-Inequality-for-Disjoint-Principal-Minors-of-Wishart-Matrices-October-8-2026/lean"
  roots := #[`WishartBlocks, `MainTheorems.WishartBlocks]
  globs := #[`WishartBlocks, `MainTheorems.WishartBlocks.+]

@[default_target]
lean_lib Chollet where
  srcDir := "preprints/Chollets-Permanent-Inequality-for-Hermitian-Matrices-Whose-Comparison-Matrices-Are-Positive-Semidefinite-October-8-2026/lean"
  roots := #[`Chollet, `MainTheorems.Chollet]
  globs := #[`Chollet, `MainTheorems.Chollet.+]

@[default_target]
lean_lib Tuza where
  srcDir := "preprints/Tuzas-Conjecture-Holds-for-Co-Chain-Graphs-October-8-2026/lean"
  roots := #[`Tuza, `MainTheorems.Tuza]
  globs := #[`Tuza, `MainTheorems.Tuza.+]

@[default_target]
lean_lib PureOSequences where
  srcDir := "preprints/Log-Concavity-of-Pure-O-Sequences-of-Given-Codimension-and-Type-October-8-2026/lean"
  roots := #[`PureOSequences, `MainTheorems.PureOSequences]
  globs := #[`PureOSequences, `MainTheorems.PureOSequences.+]

@[default_target]
lean_lib Domination where
  srcDir := "preprints/Ultra-Log-Concavity-of-the-Domination-Sequences-of-Powers-of-Paths-and-Cycles-October-9-2026/lean"
  roots := #[`Domination, `MainTheorems.Domination, `MainTheorems.LogConcavity]
  globs := #[`Domination, `MainTheorems.Domination.+, `MainTheorems.LogConcavity]

@[default_target]
lean_lib Hypercomb where
  srcDir := "preprints/Zeros-of-the-Independence-Polynomials-of-Uniform-Linear-Hypercombs-October-9-2026/lean"
  roots := #[`Hypercomb, `MainTheorems.Hypercomb]
  globs := #[`Hypercomb, `MainTheorems.Hypercomb.+]

@[default_target]
lean_lib AHOConstants where
  srcDir := "preprints/Optimal-Constants-in-the-Ando-Hiai-Okubo-Trace-Inequality-October-9-2026/lean"
  roots := #[`AHOConstants, `MainTheorems.AHOConstants]
  globs := #[`AHOConstants, `MainTheorems.AHOConstants.+]

@[default_target]
lean_lib Corona where
  srcDir := "preprints/Universal-Unimodality-of-Independence-Polynomials-of-Coronas-October-9-2026/lean"
  roots := #[`Corona, `MainTheorems.Corona]
  globs := #[`Corona, `MainTheorems.Corona.+]

@[default_target]
lean_lib SIBO where
  srcDir := "preprints/Optimal-Proximity-for-Finite-Forbidden-Labels-in-SIBO-Matroids-October-9-2026/lean"
  roots := #[`SIBO, `MainTheorems.BasisPairing, `MainTheorems.Characters, `MainTheorems.FiniteInterpolation, `MainTheorems.MixedRadix, `MainTheorems.PrefixPoints, `MainTheorems.ProductKernel, `MainTheorems.RadixLabels, `MainTheorems.SIBOKernel, `MainTheorems.SIBOProximity, `MainTheorems.SIBOSharpness, `MainTheorems.SIOrders, `MainTheorems.UniformMatroid]
  globs := #[`SIBO, `MainTheorems.BasisPairing, `MainTheorems.Characters, `MainTheorems.FiniteInterpolation, `MainTheorems.MixedRadix, `MainTheorems.PrefixPoints, `MainTheorems.ProductKernel, `MainTheorems.RadixLabels, `MainTheorems.SIBOKernel, `MainTheorems.SIBOProximity, `MainTheorems.SIBOSharpness, `MainTheorems.SIOrders, `MainTheorems.UniformMatroid]

@[default_target]
lean_lib DominationRoots where
  srcDir := "preprints/Domination-Polynomials-with-Only-Real-Roots-October-9-2026/lean"
  roots := #[`DominationRoots, `MainTheorems.DominationRoots]
  globs := #[`DominationRoots, `MainTheorems.DominationRoots.+]

@[default_target]
lean_lib EulerianPencil where
  srcDir := "preprints/Real-Zeros-of-An-x-plus-k-x-An-minus-2-x-and-a-Conjecture-of-Zhang-October-9-2026/lean"
  roots := #[`EulerianPencil, `MainTheorems.EulerianPencil]
  globs := #[`EulerianPencil, `MainTheorems.EulerianPencil.+]

@[default_target]
lean_lib PathCycleTuza where
  srcDir := "preprints/Tuzas-Conjecture-for-Powers-of-Paths-and-Cycles-October-9-2026/lean"
  roots := #[`PathCycleTuza, `MainTheorems.PathCycleTuza]
  globs := #[`PathCycleTuza, `MainTheorems.PathCycleTuza.+]


@[default_target]
lean_lib AlternativeQCharlier where
  srcDir := "preprints/Fibonacci-Positivity-of-the-Alternative-q-Charlier-Specialization-October-13-2026/lean"
  roots := #[`AlternativeQCharlier]
  globs := #[`AlternativeQCharlier, `AlternativeQCharlier.+]

@[default_target]
lean_lib AperyMoments where
  srcDir := "preprints/Apery-Polynomials-as-Stieltjes-Moment-Sequences-October-13-2026/lean"
  roots := #[`AperyMoments]
  globs := #[`AperyMoments, `AperyMoments.+]

@[default_target]
lean_lib ASR312 where
  srcDir := "preprints/Enumeration-of-Extendably-312-Avoiding-Alternating-Sign-Rectangles-October-12-2026/lean"
  roots := #[`ASR312]
  globs := #[`ASR312, `ASR312.+]

@[default_target]
lean_lib BoseBurton where
  srcDir := "preprints/Log-Concavity-of-Inverse-Z-Polynomials-of-Bose-Burton-Matroids-October-12-2026/lean"
  roots := #[`BoseBurton]
  globs := #[`BoseBurton, `BoseBurton.+]

@[default_target]
lean_lib CircleKernel where
  srcDir := "preprints/Nonvanishing-of-the-Residues-of-the-Heat-Kernel-for-a-Logarithmic-Laplacian-on-the-Circle-October-13-2026/lean"
  roots := #[`CircleKernel, `CircleResidues]
  globs := #[`CircleKernel, `CircleKernel.+, `CircleResidues, `CircleResidues.+]

@[default_target]
lean_lib CokernelPolynomiality where
  srcDir := "preprints/Polynomial-Counts-of-Cokernel-Closed-Subcategories-with-Fixed-First-Column-Defect-October-13-2026/lean"
  roots := #[`CokernelPolynomiality]
  globs := #[`CokernelPolynomiality, `CokernelPolynomiality.+]

@[default_target]
lean_lib Fan where
  srcDir := "preprints/Strict-Log-Concavity-of-Inverse-Z-Polynomials-of-Fan-Matroids-October-12-2026/lean"
  roots := #[`Fan, `ThagomizerTuran]
  globs := #[`Fan, `Fan.+, `ThagomizerTuran.+]

@[default_target]
lean_lib HankelAutomaticity where
  srcDir := "preprints/Automaticity-of-Hankel-Determinants-of-the-Binary-Sum-of-Digits-Modulo-Powers-of-Two-October-13-2026/lean"
  roots := #[`HankelAutomaticity]
  globs := #[`HankelAutomaticity, `HankelAutomaticity.+]

@[default_target]
lean_lib OscillatoryRecurrence where
  srcDir := "preprints/Symbolic-Recurrence-Coefficients-for-the-Oscillatory-Weight-x-exp-i-m-pi-x-October-13-2026/lean"
  roots := #[`OscillatoryRecurrence]
  globs := #[`OscillatoryRecurrence, `OscillatoryRecurrence.+]

@[default_target]
lean_lib Paving where
  srcDir := "preprints/Strict-Log-Concavity-of-Inverse-Z-Polynomials-of-Paving-Matroids-October-12-2026/lean"
  roots := #[`Paving]
  globs := #[`Paving, `Paving.+]

@[default_target]
lean_lib PenneyDensity where
  srcDir := "preprints/The-Density-of-Suffix-Replaceable-Pairs-in-Penneys-Ante-October-13-2026/lean"
  roots := #[`PenneyDensity]
  globs := #[`PenneyDensity, `PenneyDensity.+]

@[default_target]
lean_lib PowerWeights where
  srcDir := "preprints/Order-Zero-Operators-and-Irreducibility-of-Power-Related-Matrix-Weights-October-13-2026/lean"
  roots := #[`PowerWeights]
  globs := #[`PowerWeights, `PowerWeights.+]

@[default_target]
lean_lib ReciprocalQGamma where
  srcDir := "preprints/Strict-Sign-Regularity-of-the-Reciprocal-Jackson-q-Gamma-Kernel-October-13-2026/lean"
  roots := #[`ReciprocalQGamma]
  globs := #[`ReciprocalQGamma, `ReciprocalQGamma.+]

@[default_target]
lean_lib Dowling where
  srcDir := "preprints/Log-Concavity-of-Inverse-Z-Polynomials-of-Dowling-Matroids-with-Arbitrary-Joints-October-12-2026/lean"
  roots := #[`Dowling]
  globs := #[`Dowling, `Dowling.+]

@[default_target]
lean_lib WeakClergyman where
  srcDir := "preprints/A-Uniform-Discrepancy-Bound-for-Anti-Recurrence-Sequences-October-13-2026/lean"
  roots := #[`WeakClergyman]
  globs := #[`WeakClergyman, `WeakClergyman.+]

@[default_target]
lean_lib R32SunCounterexample where
  srcDir := "preprints/Circular-Permutations-of-Finite-Fields-with-Primitive-Adjacent-Products-October-10-2026/lean"
  roots := #[`R32SunCounterexample]
  globs := #[`R32SunCounterexample]

@[default_target]
lean_lib R34 where
  srcDir := "preprints/Log-Concavity-of-Independence-Polynomials-of-Caterpillars-October-10-2026/lean"
  roots := #[`R34]
  globs := #[`R34, `R34.+]

@[default_target]
lean_lib ArithmeticSections where
  srcDir := "preprints/Positive-Lebesgue-Measure-of-an-Arithmetic-Set-for-Constant-Non-Central-Sections-October-12-2026/lean"
  roots := #[`ArithmeticSections]
  globs := #[`ArithmeticSections, `ArithmeticSections.+, `ArithmeticSectionsTests.+]
  moreLeanArgs := #["--trust=0", "-DautoImplicit=false", "-DwarningAsError=true"]

@[default_target]
lean_lib GenericValueSemigroups where
  srcDir := "preprints/Generic-Value-Semigroups-with-Prescribed-Coordinate-Orders-October-12-2026/lean"
  roots := #[`GenericValueSemigroups]
  globs := #[`GenericValueSemigroups, `GenericValueSemigroups.+, `GenericValueSemigroupsTests.+]

@[default_target]
lean_lib BuchweitzProfiles where
  srcDir := "preprints/Numerical-Semigroups-of-Depth-Two-with-Prescribed-Buchweitz-Profiles-October-12-2026/lean"
  roots := #[`BuchweitzProfiles]
  globs := #[`BuchweitzProfiles, `BuchweitzProfiles.+, `BuchweitzProfilesTests]

@[default_target]
lean_lib ChowlaCosine where
  srcDir := "preprints/Chowlas-Cosine-Problem-with-Near-Unit-Coefficients-October-12-2026/lean"
  roots := #[`ChowlaCosine]
  globs := #[`ChowlaCosine, `ChowlaCosine.+, `ChowlaCosineTests.+]

@[default_target]
lean_lib RandomWalkSearch where
  srcDir := "preprints/Checking-and-Update-Costs-in-Random-Walk-Search-with-Several-Marked-States-October-12-2026/lean"
  roots := #[`RandomWalkSearch]
  globs := #[`RandomWalkSearch, `RandomWalkSearch.+, `RandomWalkSearchTests.+]
  moreLeanArgs := #["--trust=0", "-DautoImplicit=false", "-DwarningAsError=true"]

@[default_target]
lean_lib EmbeddingDimensionStrata where
  srcDir := "preprints/Embedding-Dimension-Strata-in-a-Space-of-Complete-Subalgebras-of-Power-Series-October-12-2026/lean"
  roots := #[`EmbeddingDimensionStrata]
  globs := #[`EmbeddingDimensionStrata, `EmbeddingDimensionStrata.+]
  moreLeanArgs := #["--trust=0", "-DautoImplicit=false", "-DwarningAsError=true"]

@[default_target]
lean_lib HonestEmbeddingDimension where
  srcDir := "preprints/The-Honest-Embedding-Dimension-of-Numerical-Semigroups-of-Multiplicity-Five-October-12-2026/lean"
  roots := #[`HonestEmbeddingDimension]
  globs := #[`HonestEmbeddingDimension, `HonestEmbeddingDimension.+, `HonestEmbeddingDimensionTests.+]

@[default_target]
lean_lib HilbertBipartite where
  srcDir := "preprints/Hilbert-Coefficients-of-Complete-Bipartite-Quadratic-Ideals-October-12-2026/lean"
  roots := #[`HilbertBipartite]
  globs := #[`HilbertBipartite, `HilbertBipartite.+, `HilbertBipartiteTests.+]
  moreLeanArgs := #["--trust=0", "-DautoImplicit=false", "-DwarningAsError=true"]

@[default_target]
lean_lib FourGeneratedSemigroups where
  srcDir := "preprints/Type-and-Relations-of-Four-Generated-Numerical-Semigroups-October-12-2026/lean"
  roots := #[`FourGeneratedSemigroups]
  globs := #[`FourGeneratedSemigroups, `FourGeneratedSemigroups.+, `FourGeneratedSemigroupsTests.+]

@[default_target]
lean_lib EdgeColoringMixing where
  srcDir := "preprints/Strong-Spatial-Mixing-for-Edge-Colorings-of-Trees-October-12-2026/lean"
  roots := #[`EdgeColoringMixing]
  globs := #[`EdgeColoringMixing, `EdgeColoringMixing.+, `EdgeColoringMixingTests.+]
  moreLeanArgs := #["--trust=0", "-DautoImplicit=false", "-DwarningAsError=true"]

@[default_target]
lean_lib TerminalLogConcavity where
  srcDir := "preprints/Strong-Terminal-Failures-of-Log-Concavity-in-Independence-Polynomials-of-Subcubic-Trees-October-12-2026/lean"
  roots := #[`TerminalLogConcavity]
  globs := #[`TerminalLogConcavity, `TerminalLogConcavity.+, `TerminalLogConcavityTests, `TerminalLogConcavityTests.+]

@[default_target]
lean_lib SphericalTreeFailures where
  srcDir := "preprints/Nearly-Linear-Consecutive-Log-Concavity-Failures-in-Spherically-Symmetric-Subcubic-Trees-October-12-2026/lean"
  roots := #[`SphericalTreeFailures]
  globs := #[`SphericalTreeFailures, `SphericalTreeFailures.+, `SphericalTreeFailuresTests]
  moreLeanArgs := #["--trust=0", "-DautoImplicit=false", "-DwarningAsError=true"]

@[default_target]
lean_lib HardCoreActivityThreshold where
  srcDir := "preprints/The-Exact-Activity-Threshold-for-Spectral-Independence-of-the-Hard-Core-Model-on-Trees-October-12-2026/lean"
  roots := #[`HardCoreActivityThreshold]
  globs := #[`HardCoreActivityThreshold, `HardCoreActivityThreshold.+, `HardCoreActivityThresholdTests.+]
  moreLeanArgs := #["--trust=0", "-DautoImplicit=false", "-DwarningAsError=true"]

@[default_target]
lean_lib SumsetRanges where
  srcDir := "preprints/Ordinary-and-Restricted-Sumset-Sizes-Beyond-a-Polynomial-Threshold-October-12-2026/lean"
  roots := #[`SumsetRanges]
  globs := #[`SumsetRanges, `SumsetRanges.+, `SumsetRangesTests.+]
  moreLeanArgs := #["--trust=0", "-DautoImplicit=false", "-DwarningAsError=true"]

@[default_target]
lean_lib MeanMaximumForests where
  srcDir := "preprints/A-Mean-Maximum-Inequality-for-Independent-Sets-of-Forests-October-12-2026/lean"
  roots := #[`MeanMaximumForests]
  globs := #[`MeanMaximumForests, `MeanMaximumForests.+, `ForestHardCoreActivityThreshold, `MeanMaximumForestsTests, `MeanMaximumForestsTests.+]
  moreLeanArgs := #["--trust=0", "-DautoImplicit=false", "-DwarningAsError=true"]

@[default_target]
lean_lib FugledeCertificates where
  srcDir := "preprints/Fugledes-Conjecture-Holds-in-F2-7-October-6-2026/lean"
  roots := #[`FugledeCertificates]
  globs := #[`FugledeCertificates, `FugledeCertificates.+]

private def runProofCheck (args : List String) (file : String) : ScriptM UInt32 := do
  let [libraryName] := args | do
    IO.eprintln "Specify one library target."
    return 1
  let some lib ← findLeanLib? (Lean.Name.mkSimple libraryName) | do
    IO.eprintln s!"Unknown library target: {libraryName}"
    return 1
  let source := lib.srcDir / file
  unless ← source.pathExists do
    IO.eprintln s!"Check file does not exist: {file}"
    return 1
  let child ← IO.Process.spawn {
    cmd := (← getLean).toString
    args := #["-j1"] ++ lib.leanArgs ++ #["-R", lib.srcDir.toString, source.toString]
    env := ← getAugmentedEnv
  }
  child.wait

script audit args do
  let [libraryName] := args | do
    IO.eprintln "Usage: lake script run audit <library>"
    return 1
  let some lib ← findLeanLib? (Lean.Name.mkSimple libraryName) | do
    IO.eprintln s!"Unknown library target: {libraryName}"
    return 1
  let file := if ← (lib.srcDir / "Audit.lean").pathExists then
    "Audit.lean" else "tests/Axioms.lean"
  runProofCheck args file

script certificates args do
  runProofCheck args "tests/Certificates.lean"
